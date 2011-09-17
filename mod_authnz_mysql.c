/*
 * Copyright (c) 2001 by J. R. Westmoreland <jr@jrw.org>
 * Portions Copyright (c) 2002-2004 by Matthew Palmer <mpalmer@debian.org>
 *
 * Original module/version: mod_authnz_mysql v2.20
 * Originally written and maintained by Zeev Suraski <bourbon@netvision.net.il>
 * A couple of fixes by Marschall Peter <Peter.Marschall@gedos.de>
 * and Brent Metz <bmetz@thor.tjhsst.edu>
 * MySQL/PHP style MD5 hashes, and an integration with the mod-auth-mysql
 * maintained by Bill Joned by Matthew Palmer <mpalmer@debian.org>
 *
 * This version maintained by Matthew Palmer <mpalmer@debian.org>
 *
 * Please read the INSTALL and USAGE files for further information.
 * 
 * 2004-02-01 MURAKAMI, takeshi <takeshi@softagency.co.jp>
 * add port, socket
 * 2004-02-07 MURAKAMI, takeshi <takeshi@softagency.co.jp>
 * apache2
 * 2004-09-20 Joseph Walton <joe@kafsemo.org>
 * SHA1 hash support
 * 2011-09-  Christopher Dyck <christopher.dyck@gmail.com>
 * Drop Apache 1.x support and make compatible to mod_authnz architecture
 *
 */

 
#define AUTHNZ_MYSQL_VERSION "1.0"

#define PALLOC apr_palloc
#define PCALLOC apr_pcalloc
#define SNPRINTF apr_snprintf
#define PSTRDUP apr_pstrdup
#define PSTRCAT apr_pstrcat
#define APACHELOG(severity, handle, message...) ap_log_error(APLOG_MARK, APLOG_NOERRNO | severity, 0, handle->server, message)

#include <ap_provider.h>

#include "config.h"

#include <httpd.h>
#include <http_config.h>
#include <http_core.h>
#include <http_protocol.h>
#include <http_log.h>
#include <mod_auth.h>

#include <http_request.h>   /* for ap_hook_(check_user_id | auth_checker)*/
#include <apr_general.h>
#include <apr_md5.h>
#include <apr_sha1.h>
#include <apr_strings.h>


#if APR_HAS_THREADS
#include <apr_thread_mutex.h>
#endif

#include <mysql.h>
#include <errmsg.h>
#include <mysqld_error.h>

#ifdef HAVE_CRYPT_H
#include <crypt.h>
#endif

#ifndef TRUE
#define TRUE 1
#endif
#ifndef FALSE
#define FALSE 0
#endif

/* This are the system-wide config options; the more specific options live in
 * a authn_mysql_config_t structure, one for each MySQL-configured directory.
 */
static char	*auth_db_host = NULL,
		*auth_db_name = NULL,
		*auth_db_user = NULL,
		*auth_db_pwd = NULL;

static int	auth_db_override = 1;

char *tmp_host = NULL;
char *auth_db_socket = NULL;
long auth_db_port = -1;
unsigned long auth_db_client_flag = 0;

/* Support for general-purpose encryption schemes.  Should be fairly straightforward.
 * We have a checking routine and a name for it (for AuthMySQL_Encryption_Types).
 */

#define PLAINTEXT_ENCRYPTION_FLAG	1<<0
#ifdef CRYPT_DES
#define CRYPT_DES_ENCRYPTION_FLAG	1<<1
#endif
#define MYSQL_ENCRYPTION_FLAG		1<<2
#ifdef CRYPT_MD5
#define CRYPT_MD5_ENCRYPTION_FLAG	1<<3
#endif
#define PHP_MD5_ENCRYPTION_FLAG		1<<4
#ifdef HAVE_CRYPT_H
#define CRYPT_ENCRYPTION_FLAG		1<<5
#endif
#define SHA1SUM_ENCRYPTION_FLAG		1<<6
#define APACHE_ENCRYPTION_FLAG		1<<7

/* from include/sha1.h from the mysql-server source distribution */
#define SHA1_HASH_SIZE 20 /* Hash size in bytes */

static int check_no_encryption(const char *passwd, char *enc_passwd)
{
	return (!strcmp(passwd, enc_passwd));
}


#ifdef CRYPT_DES
static int check_crypt_des_encryption(const char *passwd, char *enc_passwd)
{
	/* Ensure that MD5 passwords aren't checked here */
	if (!strncmp(enc_passwd, "$1$", 3)) {
		return 0;
	}
	return (!strcmp(crypt(passwd, enc_passwd), enc_passwd));
}
#endif

#ifdef CRYPT_MD5
static int check_crypt_MD5_encryption(const char *passwd, char *enc_passwd)
{
	/* Make sure only MD5 passwords are checked */
	if (strncmp(enc_passwd, "$1$", 3)) {
		return 0;
	}
	return (!strcmp(crypt(passwd, enc_passwd), enc_passwd));
}
#endif

#ifdef HAVE_CRYPT_H
static int check_crypt_encryption(const char *passwd, char *enc_passwd)
{
	return (!strcmp(crypt(passwd, enc_passwd), enc_passwd));
}
#endif

char hex_digit(char c)
{
	if (c < 10) {
		return c+'0';
	} else {
		return c-10+'a';
	}
}

static char *md5_hex_hash(const char *pass)
{
	unsigned char hash[16];
	/* This makes this function *very* specialised.  Change this to
	 * use dynamic memory if you want to reuse it somewhere else */
	static char real_hash[33];
	int i;
	apr_md5_ctx_t ct;
	apr_md5_init(&ct);
	apr_md5_update(&ct, pass, strlen(pass));
	apr_md5_final(hash, &ct);
	
	/* Now we convert the 16 octet hash to a 32 byte hex string */
	for (i = 0; i < 16; i++) {
		real_hash[2*i+1] = hash[i] & 0xF;
		real_hash[2*i] = (hash[i] & 0xF0) >> 4;
	}
	for (i = 0; i < 32; i++) {
		real_hash[i] = hex_digit(real_hash[i]);
	}
	real_hash[32] = '\0';

	return real_hash;
}

static int check_PHP_MD5_encryption(const char *passwd, char *enc_passwd)
{
	return (!strcmp(md5_hex_hash(passwd), enc_passwd));
}

static char *sha1_hex_hash(const char *passwd)
{
	int i;

	apr_sha1_ctx_t ct;
	char hash[APR_SHA1_DIGESTSIZE];
	static char real_hash[APR_SHA1_DIGESTSIZE * 2 + 1];

	apr_sha1_init(&ct);
	apr_sha1_update(&ct, passwd, strlen(passwd));
	apr_sha1_final(hash, &ct);

	/* Now we convert the 20 octet hash to a 40 byte hex string */
	for (i = 0; i < sizeof(hash); i++) {
		real_hash[2*i+1] = hash[i] & 0xF;
		real_hash[2*i] = (hash[i] & 0xF0) >> 4;
	}
	for (i = 0; i < sizeof(real_hash); i++) {
		real_hash[i] = hex_digit(real_hash[i]);
	}
	real_hash[sizeof(real_hash)-1] = '\0';

	return real_hash;
}

static int check_SHA1Sum_encryption(const char *passwd, char *enc_passwd)
{
	return (!strcmp(sha1_hex_hash(passwd), enc_passwd));
}


static int check_mysql_encryption(const char *passwd, char *enc_passwd)
{
	char scrambled_passwd[2*SHA1_HASH_SIZE + 2];
	
	make_scrambled_password(scrambled_passwd, passwd);
	return (!strcmp(scrambled_passwd, enc_passwd));
}

static int check_apache_encryption(const char *passwd, char *enc_passwd)
{
	return (!apr_password_validate(passwd, enc_passwd));
	return (!ap_validate_password(passwd, enc_passwd));
}

typedef struct {
	char *name;
	int (*check_function)(const char *passwd, char *enc_passwd);
	int flag;
} encryption_type_entry;

encryption_type_entry supported_encryption_types[] = {
	{ "Plaintext",		check_no_encryption,			PLAINTEXT_ENCRYPTION_FLAG },
#if CRYPT_DES
	{ "Crypt_DES",		check_crypt_des_encryption,		CRYPT_DES_ENCRYPTION_FLAG },
#endif
	{ "MySQL",		check_mysql_encryption,			MYSQL_ENCRYPTION_FLAG },
#if CRYPT_MD5
	{ "Crypt_MD5",		check_crypt_MD5_encryption,		CRYPT_MD5_ENCRYPTION_FLAG },
#endif
	{ "Crypt",		check_crypt_encryption,			CRYPT_ENCRYPTION_FLAG },
	{ "PHP_MD5",		check_PHP_MD5_encryption,		PHP_MD5_ENCRYPTION_FLAG	},
	{ "SHA1Sum",	check_SHA1Sum_encryption, SHA1SUM_ENCRYPTION_FLAG},
	{ "Apache",		check_apache_encryption,		APACHE_ENCRYPTION_FLAG  },
	/* add additional encryption types below */
	{ NULL,			NULL,					0 }
};

static int get_encryption_flag(const char *name)
{
	register encryption_type_entry *ete=supported_encryption_types;
	
	while (ete->name) {
		if (!strcmp(ete->name, name)) {
			return ete->flag;
		}
		ete++;
	}
	return 0;
}

/* end of support for general-purpose encryption schemes */

/* Per-directory configuration structure.  One of these is created for each
 * <Directory>...</Directory> and .htaccess file which requests authentication
 */
typedef struct {
	char *dir;

	char *db_host;
	char *db_socket;
	unsigned int db_port;
	char *db_user;
	char *db_pwd;
	char *db_name;
	char *db_charset;
	
	MYSQL *dbh;

#if APR_HAS_THREADS	
	apr_thread_mutex_t *lock;       /* Lock for this config */
#endif

	/* Boolean options */
	unsigned char persistent;
	unsigned char enable_mysql_auth;

	/* Some MySQL errors are retryable; if we retry the operation
	 * by recursing into the same function, we set this so we don't
	 * recurse indefinitely if it's a permanent error.
	 */
	unsigned char dbh_error_lastchance;

	char *user_table;
	char *group_table;

	char *user_field;
	char *password_field;
	char *group_field;
	char *group_user_field;
	char *group_where_clause;
	char *password_where_clause;
		
	int encryption_types;
	unsigned char using_encryption_types;

	unsigned char allow_empty_passwords;
	unsigned char authoritative;

	/* You're not going to believe this, but, near as I can tell, apache
	 * doesn't respect the last part of the config_rec.  May be an
	 * underflow in some code somewhere, but I'm not taking no chances
	 * with *my* config variables...
	 */
	char sacrificial_lamb[15];

} authn_mysql_config_t;

module authnz_mysql_module;

static int open_authnz_dblink(request_rec *r, authn_mysql_config_t *sec);

static apr_status_t authnz_mysql_cleanup(void *ptr)
{
	authn_mysql_config_t *sec = ptr;

	if (sec->dbh) {
#ifdef DEBUG
		syslog(LOG_DEBUG, "MAMDEBUG: Closing MySQL connection");
#endif
		mysql_close(sec->dbh);
		sec->dbh = NULL;
	}
}

/* Removed mysql_authnz_init_handler
 */

/* Called each and every time a new per-directory configuration is
 * created.  We just initialise variables and set defaults.  This is
 * run *before* actual config takes place.
 */
void *create_authnz_mysql_dir_config(apr_pool_t *p, char *d)
{
#ifdef DEBUG
	int i;
#endif

	authn_mysql_config_t *sec = (authn_mysql_config_t *) PCALLOC(p, sizeof(authn_mysql_config_t));
	
#ifdef DEBUG
	syslog(LOG_DEBUG, "MAMDEBUG: Now configuring server config for %s", d);
	syslog(LOG_DEBUG, "MAMDEBUG: sizeof(authn_mysql_config_t) = %i",
				sizeof(authn_mysql_config_t));
#endif

	sec->db_name = sec->db_socket = sec->db_user = sec->db_pwd = sec->db_charset = NULL;

	sec->dbh = NULL;
	/* When the memory for this connection record is cleaned, we must
	 * be sure to close the DB connection, if it exists.  If this does
	 * not happen, we are in a world of pain.
	 */

	apr_pool_cleanup_register(p, sec, authnz_mysql_cleanup, apr_pool_cleanup_null);

#if APR_HAS_THREADS	
	apr_thread_mutex_create(&sec->lock, APR_THREAD_MUTEX_DEFAULT, p);
#endif

	sec->dir = d;
	
	sec->user_table = sec->group_table = NULL;
	sec->user_field = sec->password_field = sec->group_field = NULL;
	sec->group_where_clause = sec->password_where_clause = NULL;
	sec->group_user_field = NULL;
	
	sec->authoritative = 1;
	sec->allow_empty_passwords = 1;

	sec->dbh_error_lastchance = 0;

#ifdef DEBUG
	syslog(LOG_DEBUG, "MAMDEBUG: Enabling MySQL auth by default");
#endif
	sec->enable_mysql_auth = 1;

#ifdef CRYPT_DES
	sec->encryption_types = CRYPT_DES_ENCRYPTION_FLAG;
	sec->using_encryption_types = 0;
#else
	sec->encryption_types = 0;
	sec->using_encryption_types = 0;
#endif

	sec->db_port = -1;
	
#ifdef DEBUG
	syslog(LOG_DEBUG, "MAMDEBUG: Persistent is now ON");
#endif
	sec->persistent = 1;

#ifdef DEBUG
	for (i = 0; i < 15; i++)
	{
		sec->sacrificial_lamb[i] = i % 10 + '0';
	}
#endif
	
	return sec;
}

/* Ensure that any string passed through us won't unduly upset the MySQL
 * server when passed in as part of a query.
 */
static char *mysql_escape(authn_mysql_config_t *sec, request_rec *r, const char *str, apr_pool_t *p)
{
	char *dest;
	
	if (!str) {
		return NULL;
	}

	dest = (char *) PALLOC(p, strlen(str) * 2 + 1);
	if (!dest) {
		return str;
	}
	
	mysql_real_escape_string(sec->dbh, dest, str, strlen(str));
	
	return dest;
}

/* Config helper to set the server-wide default database name.
 */
static const char *set_authnz_mysql_db(cmd_parms * parms, void *dummy, const char *db)
{
	auth_db_name = (char *)db;
	return NULL;
}

/* Config helper to set the server-wide default database host.
 */
static const char *set_authnz_mysql_host(cmd_parms *parms, void *dummy, const char *host)
{
	auth_db_host = (char *) host;
	return NULL;
}

/* Config helper to set server-wide defaults for database parameters.
 */
static const char *set_authnz_mysql_info(cmd_parms * parms, void *dummy, const char *host, const char *user, const char *pwd)
{
	if (*host != '.') {
		auth_db_host = (char *) host;
	}

	if (*user != '.') {
		auth_db_user = (char *)user;
	}

	if (*pwd != '.') {
		auth_db_pwd = (char *)pwd;
	}

	return NULL;
}

/* Config helper to set the server-wide default database username.
 */
static const char *set_authnz_mysql_user(cmd_parms *parms, void *dummy, const char *user)
{
	auth_db_user = (char *)user;
	return NULL;
}

/* Config helper to set the server-wide default database password (coupled to
 * the user specified above).
 */
static const char *set_authnz_mysql_pwd(cmd_parms *parms, void *dummy, const char *pwd)
{
	auth_db_pwd = (char *)pwd;
	return NULL;
}

/* Set the server-wide database server socket.
 */
static const char *set_authnz_mysql_socket(cmd_parms *parms, void *dummy, const char *sock)
{
	auth_db_socket = (char *)socket;
	return NULL;
}

/* Set the server-wide database server port.
 */
static const char *set_authnz_mysql_port(cmd_parms *parms, void *dummy, const char *port)
{
	auth_db_port = (unsigned int) atoi(port);
	return NULL;
}

/* Config helper to judge whether to allow per-directory configs to override
 * the server-wide defaults for database parameters.  The only reason this
 * exists (instead of using an ap_set_flag_slot) is because this isn't part
 * of a config structure, and I'm not sure how to set globals from the Apache
 * config thing.
 */
static const char *set_authnz_mysql_override(cmd_parms *parms, void *dummy, int arg)
{
	auth_db_override = arg;
	return NULL;
}

/* Config helper to set a selected encryption type.
 */
static const char *set_encryption_types(cmd_parms *cmd, void *sconf, const char *arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	int new_encryption_flag = get_encryption_flag(arg);

	if (!new_encryption_flag) {
		APACHELOG(APLOG_ERR, cmd, "Unsupported encryption type: %s", arg);
		return NULL;
	}

	if (!sec->using_encryption_types) {
		sec->encryption_types = 0;
		sec->using_encryption_types = 1;
	}
	
	sec->encryption_types |= new_encryption_flag;
	
	return NULL;
}

/* This pair of config helpers exist only because of varying semantics
 * in the two versions of mod_authnz_mysql I merged.  As soon as we have a
 * consistent set of configuration primitives, these are going.
 */
static const char *set_non_persistent(cmd_parms *cmd, void *sconf, int arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	sec->persistent = !arg;
	APACHELOG(APLOG_DEBUG, cmd, "set_non_persistent: Setting persistent in %s to %i", sec->dir, sec->persistent);
	return NULL;
}

static const char *set_persistent(cmd_parms *cmd, void *sconf, int arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	sec->persistent = arg;
	APACHELOG(APLOG_DEBUG, cmd, "set_persistent: Setting persistent in %s to %i", sec->dir, sec->persistent);
	return NULL;
}

static const char *enable_mysql(cmd_parms *cmd, void *sconf, int arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	sec->enable_mysql_auth = arg;
	APACHELOG(APLOG_DEBUG, cmd, "enable_mysql: Setting enable_mysql_auth in %s to %i", sec->dir, sec->enable_mysql_auth);
	return NULL;
}

static const char *set_empty_passwords(cmd_parms *cmd, void *sconf, int arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	sec->allow_empty_passwords = arg;
	APACHELOG(APLOG_DEBUG, cmd, "set_empty_passwords: Setting allow_empty_passwords in %s to %i", sec->dir, sec->allow_empty_passwords);
	return NULL;
}

static const char *set_authoritative(cmd_parms *cmd, void *sconf, int arg)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) sconf;

	sec->authoritative = arg;
	APACHELOG(APLOG_DEBUG, cmd, "set_authoritative: Setting authoritative in %s to %i", sec->dir, sec->authoritative);
	return NULL;
}

/* The command list.  What it's called, when it's legal to use it, and
 * what to do when we find it.  Pretty cool, IMHO.
 */

static
command_rec authnz_mysql_cmds[] = {
   AP_INIT_TAKE3( "AuthMySQL_Info",	set_authnz_mysql_info,
   		  NULL,
   		  RSRC_CONF,	"host, user and password of the MySQL database" ),

   AP_INIT_TAKE1( "AuthMySQL_DefaultHost",	set_authnz_mysql_host,
		  NULL,
		  RSRC_CONF,	"Default MySQL host" ),

   AP_INIT_TAKE1( "AuthMySQL_DefaultUser",	set_authnz_mysql_user,
		  NULL,
		  RSRC_CONF,	"Default MySQL user" ),

   AP_INIT_TAKE1( "AuthMySQL_DefaultPassword",	set_authnz_mysql_pwd,
		  NULL,
		  RSRC_CONF,	"Default MySQL password" ),

   AP_INIT_TAKE1( "AuthMySQL_DefaultPort",	set_authnz_mysql_port,
		  NULL,
		  RSRC_CONF,	"Default MySQL server port" ),
	

	  	
   AP_INIT_TAKE1( "AuthMySQL_DefaultSocket",	set_authnz_mysql_socket,
		  NULL,
		  RSRC_CONF,	"Default MySQL server socket" ),


   AP_INIT_TAKE1( "AuthMySQL_General_DB",	set_authnz_mysql_db,
		  NULL,
		  RSRC_CONF,	"default database for MySQL authentication" ),


   AP_INIT_TAKE1( "AuthMySQL_DefaultDB",	set_authnz_mysql_db,
		  NULL,
		  RSRC_CONF,	"default database for MySQL authentication" ),


   AP_INIT_TAKE1( "AuthMySQL_Host",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_host),
		  OR_AUTHCFG,	"database host" ),

   AP_INIT_TAKE1( "AuthMySQL_Socket",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_socket),
		  OR_AUTHCFG,	"database host socket" ),


   AP_INIT_TAKE1( "AuthMySQL_Port",	ap_set_int_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_port),
		  OR_AUTHCFG,	"database host port" ),

   AP_INIT_TAKE1( "AuthMySQL_Username",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_user),
		  OR_AUTHCFG,	"database user" ),

   AP_INIT_TAKE1( "AuthMySQL_User",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_user),
		  OR_AUTHCFG,	"database user" ),

   AP_INIT_TAKE1( "AuthMySQL_Password",			ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_pwd),
		  OR_AUTHCFG,	"database password" ),

   AP_INIT_TAKE1( "AuthMySQL_DB",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_name),
		  OR_AUTHCFG,	"database name" ),

   AP_INIT_TAKE1( "AuthMySQL_CharacterSet",	ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, db_charset),
		  OR_AUTHCFG,	"character set" ),

   AP_INIT_TAKE1( "AuthMySQL_Password_Table",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, user_table),
		  OR_AUTHCFG,	"Name of the MySQL table containing the password/user-name combination" ),

   AP_INIT_TAKE1( "AuthMySQL_Group_Table",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, group_table),
		  OR_AUTHCFG,	"Name of the MySQL table containing the group-name/user-name combination; can be the same as the password-table." ),

   AP_INIT_TAKE1( "AuthMySQL_Group_Where",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, group_where_clause),
		  OR_AUTHCFG,	"Additional WHERE clause for group/user-name lookup" ),

   AP_INIT_TAKE1( "AuthMySQL_Password_Field",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, password_field),
		  OR_AUTHCFG,	"The name of the field in the MySQL password table" ),

   AP_INIT_TAKE1( "AuthMySQL_Password_Where",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, password_where_clause),
		  OR_AUTHCFG,	"Additional WHERE clause for group password/user-name lookup" ),

   AP_INIT_TAKE1( "AuthMySQL_Username_Field",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, user_field),
		  OR_AUTHCFG,	"The name of the user-name field in the MySQL password (and possibly group) table(s)." ),

   AP_INIT_TAKE1( "AuthMySQL_Group_Field",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, group_field),
		  OR_AUTHCFG,	"The name of the group field in the MySQL group table; must be set if you want to use groups." ),

   AP_INIT_TAKE1( "AuthMySQL_Group_User_Field",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, group_user_field),
		  OR_AUTHCFG,	"The name of the user-name field in the MySQL group table; defaults to the same as the username field for the password table." ),

   AP_INIT_FLAG( "AuthMySQL_Empty_Passwords",		set_empty_passwords,
		 NULL,
		 OR_AUTHCFG,	"Enable (on) or disable (off) empty password strings; in which case any user password is accepted." ),

   AP_INIT_FLAG( "AuthMySQL_Authoritative",		set_authoritative,
		 NULL,
		 OR_AUTHCFG,	"When 'on' the MySQL database is taken to be authoritative and access control is not passed along to other db or access modules." ),

   AP_INIT_FLAG( "AuthMySQL_AllowOverride",		set_authnz_mysql_override,
		 NULL,
		 RSRC_CONF,	"Allow directory overrides of configuration" ),

   AP_INIT_ITERATE( "AuthMySQL_Encryption_Types",		set_encryption_types,
		  NULL,
		  OR_AUTHCFG,	"Encryption types to use" ),

   AP_INIT_FLAG( "AuthMySQL_Non_Persistent",		set_non_persistent,
		 NULL,
		 OR_AUTHCFG,	"Use non-persistent MySQL links" ),

   AP_INIT_FLAG( "AuthMySQL_Persistent",		set_persistent,
		 NULL,
		 OR_AUTHCFG,	"Use non-persistent MySQL links" ),

   AP_INIT_FLAG( "AuthMySQL",		enable_mysql,
		 NULL,
		 OR_AUTHCFG,	"Enable MySQL authentication" ),

   AP_INIT_TAKE1( "AuthMySQL_Where",		ap_set_string_slot,
		  (void*)APR_OFFSETOF(authn_mysql_config_t, password_where_clause),
		  OR_AUTHCFG,	"Additional WHERE clause for group password/user-name lookup" ),

  { NULL }
};

static apr_status_t authnz_mysql_result_cleanup(void *result)
{
	mysql_free_result((MYSQL_RES *) result);
}


static void note_cleanups_for_mysql_authnz_result(apr_pool_t *p, MYSQL_RES * result)
{
	apr_pool_cleanup_register(p, (void *) result, authnz_mysql_result_cleanup, authnz_mysql_result_cleanup);
}

/* Make a MySQL database link open and ready for business.  Returns 0 on
 * success, or the MySQL error number which caused the failure if there was
 * some sort of problem.
 */
static int open_authnz_dblink(request_rec *r, authn_mysql_config_t *sec)
{
	char *host = "localhost", *socket = NULL;
	unsigned int port = 3306;
	char *dbname = auth_db_name, *user = auth_db_user, *pwd = auth_db_pwd;
	void (*sigpipe_handler)();
	unsigned long client_flag = 0;
#if MYSQL_VERSION_ID >= 50013
	my_bool do_reconnect = 1;
#endif
	char *query;

	APACHELOG(APLOG_DEBUG, r, "Opening DB connection for %s", sec->dir);
	
	if (auth_db_host) {
		host = auth_db_host;
	}

	if (auth_db_socket)
	{
		socket = auth_db_socket;
	}

	if (auth_db_port != -1)
	{
		port = auth_db_port;
	}
	
	if (auth_db_override)
	{
		if (sec->db_socket)
		{
			socket = sec->db_socket;
		}
	
		if (sec->db_port != -1)
		{
			port = sec->db_port;
		}
		
		if (sec->db_host)
		{
			host = sec->db_host;
		}

		if (sec->db_user) {
			user = sec->db_user;
		}

		if (sec->db_pwd) {
			pwd = sec->db_pwd;
		}

		if (sec->db_name) {
			dbname = sec->db_name;
		}
	}

	if (!dbname || !dbname[0]) {
		/* It would be preferred if we had somewhere to connect to... */
		APACHELOG(APLOG_CRIT, r,
			"No database given - rather a problem.  Bailing out.");
		return CR_WRONG_HOST_INFO;
	}

	/* MySQL likes to throw the odd SIGPIPE now and then - ignore it for now */
	sigpipe_handler = signal(SIGPIPE, SIG_IGN);
		
	sec->dbh = mysql_init(NULL);
	
	if (!mysql_real_connect(sec->dbh, host, user, pwd, dbname, port, socket, client_flag)) {
		APACHELOG(APLOG_ERR, r,
			 "Connection error: %s", mysql_error(sec->dbh));
		errno = mysql_errno(sec->dbh);
		mysql_close(sec->dbh);
		sec->dbh = NULL;
		return errno;
	}

#if MYSQL_VERSION_ID >= 50013
	/* The default is no longer to automatically reconnect on failure,
	 * (as of 5.0.3) so we have to set that option here.  The option is
	 * available from 5.0.13.  */
	mysql_options(sec->dbh, MYSQL_OPT_RECONNECT, &do_reconnect);
#endif

	signal(SIGPIPE, sigpipe_handler);
	
	APACHELOG(APLOG_DEBUG, r, "Persistent in %s is %i", sec->dir, sec->persistent);

	if (!sec->persistent) {
		APACHELOG(APLOG_DEBUG, r, "Registering non-persistent for %s", sec->dir);
		apr_pool_cleanup_register(r->pool, sec, authnz_mysql_cleanup, apr_pool_cleanup_null);
	}

	if (sec->db_charset) {
		const char *check;

		APACHELOG(APLOG_DEBUG, r,
			"Setting character set to %s", sec->db_charset);

		mysql_set_character_set(sec->dbh, sec->db_charset);

		check = mysql_character_set_name(sec->dbh);

		if (!check || strcmp(sec->db_charset, check)) {
			APACHELOG(APLOG_ERR, r,
				"Failed to set character set to %s", sec->db_charset);
			return -1;
		}
	}

	/* W00t!  We made it! */
	return 0;
}

/* Run a query against the database.  Doesn't assume nearly anything about
 * the state of affairs regarding the database connection.
 * Returns 0 on a successful query run, or the MySQL error number on
 * error.  It is the responsibility of the calling function to retrieve any
 * data which may have been obtained through the running of this function.
 */
static int safe_mysql_query(request_rec *r, char *query, authn_mysql_config_t *sec)
{
	int error = CR_UNKNOWN_ERROR;

	APACHELOG(APLOG_DEBUG, r, "sec->dbh in %s is %p", sec->dir, sec->dbh);
	if (sec->dbh_error_lastchance)
	{
		APACHELOG(APLOG_DEBUG, r, "Last chance, bub");
	}
	else
	{
		APACHELOG(APLOG_DEBUG, r, "Ordinary query");
	}
	
	if (!sec->dbh) {
		APACHELOG(APLOG_DEBUG, r,
			"No DB connection open - firing one up");
		if ((error = open_authnz_dblink(r, sec))) {
			APACHELOG(APLOG_DEBUG, r,
				"open_authnz_dblink returned %i", error);
			return error;
		}

		APACHELOG(APLOG_DEBUG, r,
			"Correctly opened a new DB connection");
	}

	APACHELOG(APLOG_DEBUG, r,
		"Running query: [%s]", query);

	if (mysql_query(sec->dbh, query)) {
		error = mysql_errno(sec->dbh);
		
		APACHELOG(APLOG_DEBUG, r, 
			"Query maybe-failed: %s (%i), lastchance=%i", mysql_error(sec->dbh), error, sec->dbh_error_lastchance);
		APACHELOG(APLOG_DEBUG, r,
			"Error numbers of interest are %i (SG) and %i (SL)",
			CR_SERVER_GONE_ERROR, CR_SERVER_LOST);
		if (sec->dbh_error_lastchance)
		{
			/* No matter what error, we're moving out */
			return error;
		}
		else if (error == CR_SERVER_LOST || error == CR_SERVER_GONE_ERROR)
		{
			/* Try again, once more only */
			sec->dbh_error_lastchance = 1;
			sec->dbh = NULL;
			APACHELOG(APLOG_DEBUG, r, "Retrying query");
			return safe_mysql_query(r, query, sec);
		}
		else
		{
			return error;
		}
	}

	return 0;
}

/* Store the result of a query in a result structure, and return it.  It's
 * "safe" in the fact that a cleanup function is registered for the structure
 * so it will be tidied up after the request.
 * Returns the result data on success, or NULL if there was no data to retrieve.
 */

static MYSQL_RES *safe_mysql_store_result(apr_pool_t *p, authn_mysql_config_t *sec)
{
	MYSQL_RES *result;
	result = mysql_store_result(sec->dbh);
#ifdef DEBUG
	syslog(LOG_DEBUG, "MAMDEBUG: Got %p for result", result);
#endif

	if (result) {
		note_cleanups_for_mysql_authnz_result(p, result);
	}
	return result;
}

/* Check the plaintext password given against the hashed version.  Go
 * through all configured encryption types looking for a match.
 * Returns 1 on a match, 0 on no match, and -1 on error.
 */
static int check_password(const char *plaintext, char *hashed, request_rec *r, authn_mysql_config_t *sec)
{
	encryption_type_entry *ete;
	
	/* empty password support */
	if (!strlen(hashed)) {
               if (sec->allow_empty_passwords) {
                       APACHELOG(APLOG_INFO, r, "User successful on empty password");
                       return AUTH_GRANTED;
               } else {
                       APACHELOG(APLOG_INFO, r, "Rejecting login because of empty password field in DB");
                       return AUTH_DENIED;
               }
        }

			
	for (ete=supported_encryption_types; ete->name; ete++) {
		if (sec->encryption_types & ete->flag) {
			APACHELOG(APLOG_DEBUG, r,
				"Checking with %s", ete->name);
			if (ete->check_function(plaintext, hashed)) {
				APACHELOG(APLOG_DEBUG, r, "Auth succeeded");
				return AUTH_GRANTED;
			}
		}
	}
	APACHELOG(APLOG_DEBUG, r, "User failed all encryption types");
	return AUTH_DENIED;
}

/* Checks whether the username and plaintext password match the user data
 * stored in the database, against all configured encryption schemes.
 * Returns 1 on successful match, 0 unsuccessful match, -1 on error.
 */
static authn_status authnz_mysql_check_password(request_rec *r, const char *user, const char *password)
{
	char *auth_table = "mysql_auth", *auth_user_field = "username",
		*auth_password_field = "passwd", *auth_password_clause = "";
	char *query;
	char *esc_user = NULL;
	MYSQL_RES *result;
	MYSQL_ROW sql_row;
	int error = CR_UNKNOWN_ERROR;
	int rv;
	authn_mysql_config_t *sec =
		(authn_mysql_config_t *)ap_get_module_config(r->per_dir_config, &authnz_mysql_module);
		
	if (!sec->dbh) {
		APACHELOG(APLOG_DEBUG, r,
			"No DB connection open - firing one up");
		if ((error = open_authnz_dblink(r, sec))) {
			APACHELOG(APLOG_DEBUG, r,
				"open_authnz_dblink returned %i", error);
			return AUTH_GENERAL_ERROR;
		}

		APACHELOG(APLOG_DEBUG, r,
			"Correctly opened a new DB connection");
	}

	esc_user = mysql_escape(sec, r, user, r->pool);

	if (sec->user_table) {
		auth_table = sec->user_table;
	}
	if (sec->user_field) {
		auth_user_field = sec->user_field;
	}
	if (sec->password_field) {
		auth_password_field = sec->password_field;
	}
	if (sec->password_where_clause) {
		auth_password_clause = sec->password_where_clause;
	}
	APACHELOG(APLOG_DEBUG, r,
		"Constructing password collection query with "
		"passfield=[%s], table=[%s], userfield=[%s], where_clause=[%s]", auth_password_field
							, auth_table, esc_user,auth_password_clause);

	query = (char *) PSTRCAT(r->pool, "SELECT ", auth_password_field,
					" FROM ", auth_table, " WHERE ",
					auth_user_field, "='", esc_user, "'",
					auth_password_clause, NULL);
	if (!query) {
		APACHELOG(APLOG_ERR, r,
			"Failed to create query string - we're in deep poopy");
		return AUTH_GENERAL_ERROR;
	}

#if APR_HAS_THREADS
        apr_thread_mutex_lock(sec->lock);
#endif

	if ((rv = safe_mysql_query(r, query, sec))) {
		if (sec->dbh)
		{
			APACHELOG(APLOG_ERR, r,
				"Query call failed: %s (%i)", mysql_error(sec->dbh), rv);
		}

		APACHELOG(APLOG_DEBUG, r, "Failed query was: [%s]", query);
		goto Error;
	}

	result = safe_mysql_store_result(r->pool, sec);
	if (!result) {
		APACHELOG(APLOG_ERR, r,
			"Failed to get MySQL result structure : %s", mysql_error(sec->dbh));
		goto Error;
	}

#if APR_HAS_THREADS	
        apr_thread_mutex_unlock(sec->lock);
#endif

	switch (mysql_num_rows(result)) {
		case 0:
			APACHELOG(APLOG_INFO, r, "User not found");
			return AUTH_USER_NOT_FOUND;
			break;
		case 1:
			sql_row = mysql_fetch_row(result);
			/* ensure we have a row, and non NULL value */
			if (!sql_row || !sql_row[0]) {
				APACHELOG(APLOG_INFO, r,
					"No row returned or NULL value: %s", mysql_error(sec->dbh));
				return AUTH_GENERAL_ERROR;
			}
			
			authn_status resv = check_password(password, sql_row[0], r, sec);
			if (resv == AUTH_DENIED)
			{
				APACHELOG(APLOG_INFO, r,
					"Authentication failed for user %s", user);
			}
			return resv;
			break;

		default:
			APACHELOG(APLOG_ERR, r,
				"Multiple password rows returned - this is what is known, in the industry, as a Bad Thing");
			return AUTH_GENERAL_ERROR;
			break;
	}

	APACHELOG(APLOG_CRIT, r, "Can't happen - dropped out of switch!");
	return AUTH_GENERAL_ERROR;

Error:
#if APR_HAS_THREADS	
        apr_thread_mutex_unlock(sec->lock);
#endif
	return AUTH_GENERAL_ERROR;
}

/* Has a look to see if the given user is a member of the named group.
 * Returns 0 if user is not a part of the group, 1 if he is, -1 on error.
 */
static int mysql_check_group(request_rec *r, char *user, char *group, authn_mysql_config_t *sec)
{
	char *auth_table = "mysql_auth", *auth_group_field="groups", *auth_group_clause="";
	char *query;
	char *esc_user = mysql_escape(sec, r, user, r->pool);
	char *esc_group = mysql_escape(sec, r, group, r->pool);
	MYSQL_RES *result;
	MYSQL_ROW row;
	char *auth_user_field = "username";

	if (!group) {
		APACHELOG(APLOG_ERR, r, "No group specified");
		return 0;
	}
	
	if (sec->group_table) {
		auth_table = sec->group_table;
	}

	if (sec->user_field)
	{
		auth_user_field = sec->user_field;
	}

	if (sec->group_user_field) {
		auth_user_field = sec->group_user_field;
	}
		
	if (sec->group_field) {
		auth_group_field = sec->group_field;
	}
	if (sec->group_where_clause) {
		auth_group_clause = sec->group_where_clause;
	}

	APACHELOG(APLOG_DEBUG, r,
		"Making group query with auth_table=[%s], auth_user_field=[%s], "
		"esc_user=[%s], esc_group=[%s], auth_group_field=[%s], where_clause=[%s]",
		auth_table, auth_user_field, esc_user, esc_group, auth_group_field,auth_group_clause);

	query = (char *) PSTRCAT(r->pool, "SELECT count(*) FROM ", auth_table,
		" WHERE ", auth_user_field, "='", esc_user, "'",
		" and FIND_IN_SET('", esc_group, "',", auth_group_field, ")",
		auth_group_clause, NULL);

	APACHELOG(APLOG_DEBUG, r, "Group query created; [%s]", query);
		
	if (!query) {
		APACHELOG(APLOG_CRIT, r,
			"Failed to create group-check query - ran out of memory!");
		return -1;
	}
	if (safe_mysql_query(r, query, sec)) {
		APACHELOG(APLOG_CRIT, r, "Group query failed!");
		return -1;
	}
	result = safe_mysql_store_result(r->pool, sec);
	if (!result || (row=mysql_fetch_row(result))==NULL || !row[0]) {
		APACHELOG(APLOG_CRIT, r, "Store result failed - erp!");
		return -1;
	}

	return atoi(row[0]);
}

/* The apache-called function.  Note that this function says nothing about
 * what the user should be allowed to do - merely that they have proved they
 * are who they say they are.  Return OK if the user has proved their
 * identity, DECLINED if we are not taking any responsibility for them, or
 * some Apache error if there was a problem.
 */
int mysql_authenticate_basic_user(request_rec *r)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) ap_get_module_config(r->per_dir_config, &authnz_mysql_module);
	conn_rec *c = r->connection;
	const char *sent_pw;
	int res;

	APACHELOG(APLOG_DEBUG, r, "Handling an authentication request for section %s", sec->dir);

#ifdef DEBUG
	for (res = 0; res < 512; res++)
	{
		if (sec->sacrificial_lamb[res] == '\0')
		{
			sec->sacrificial_lamb[res] = 'n';
		}
		if (!isgraph(sec->sacrificial_lamb[res]))
		{
			sec->sacrificial_lamb[res] = ' ';
		}
	}
	sec->sacrificial_lamb[511] = '\0';
	
	syslog(LOG_DEBUG, "The contents of the lamb are %s", sec->sacrificial_lamb);
#endif

	if (!sec->enable_mysql_auth) {
		APACHELOG(APLOG_DEBUG, r,
			"Not running mod-auth-mysql for %s - disabled", r->unparsed_uri);
		return DECLINED;
	}

	/* use MySQL auth only if we have a database */
	if (!auth_db_name && !sec->db_name) {
		APACHELOG(APLOG_ERR, r,
			"Failed to run mod-auth-mysql for %s: No database name specified", r->unparsed_uri);
		return DECLINED;
	}

	/* obtain sent password */
	if ((res = ap_get_basic_authnz_pw(r, &sent_pw))) {
		return res;
	}

	APACHELOG(APLOG_DEBUG, r,
		"Starting basic user auth for [%s] in %s, child pid %i",
		r->user,
		sec->dir, getpid());

		switch (authnz_mysql_check_password(r, r->user, sent_pw)) {
		case 0:
			ap_note_basic_authnz_failure(r);
			return HTTP_UNAUTHORIZED;
			break;
		case 1:
			return OK;
			break;
		case -1:
		default:
			APACHELOG(APLOG_DEBUG, r,
				"mysql_check_user_password returned error");
			return HTTP_INTERNAL_SERVER_ERROR;
			break;
	}
}

/* Go through a 'requires' line configured for the module, and return OK
 * if the user satisfies the line, or some sort of failure return code
 * otherwise.
 */
int check_mysql_authnz_require(char *user, const char *t, request_rec *r)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) ap_get_module_config(r->per_dir_config, &authnz_mysql_module);
	const char *w;
	int rv;
	
	w = ap_getword(r->pool, &t, ' ');
	/* If they're letting any old authenticated user, we're off the
	 * hook!
	 */
	if (!strcmp(w, "valid-user")) {
		return OK;
	}

	/* Checking a list of usernames */
	if (!strcmp(w, "user")) {
		while (t[0]) {
			w = ap_getword_conf(r->pool, &t);
			if (!strcmp(user, w)) {
				return OK;
			}
		}
		/* Not found */
		return HTTP_UNAUTHORIZED;
	} else if (!strcmp(w, "group")) {
		/* This is the prickly one; checking whether the
		 * user is a member of a listed group.
		 */
		while (t[0])
		{
			w = ap_getword_conf(r->pool, &t);
			rv = mysql_check_group(r, user, (char *)w, sec);
			
			if (rv == 1)
			{
				/* Yep, we're all good */
				return OK;
			}
			else if (rv == -1)
			{
				return HTTP_INTERNAL_SERVER_ERROR;
			}
		}
		/* Distinct lack of foundage */
		return HTTP_UNAUTHORIZED;
	}
	else
	{
		APACHELOG(APLOG_ERR, r, "Invalid argument to require: %s", w);
		return HTTP_INTERNAL_SERVER_ERROR;
	}

	APACHELOG(APLOG_ERR, r, "CAN'T HAPPEN: Dropped out of the bottom of check_mysql_authnz_require!");
	return HTTP_INTERNAL_SERVER_ERROR;
}

/* This is the authorization step.  We're presuming that the user has
 * successfully negotiated the step of "I am who I say I am", now we're
 * checking to see if the user has permission to access this particular
 * resource.  As with mysql_authenticate_basic_user, above, we return OK if
 * the user is fit to proceed, DECLINED if we don't want to make a decision
 * either way, HTTP_UNAUTHORIZED if the user is not allowed, or some apache
 * error if there was a major problem.
 */
int authnz_mysql_check_user_access(request_rec *r)
{
	authn_mysql_config_t *sec = (authn_mysql_config_t *) ap_get_module_config(r->per_dir_config, &authnz_mysql_module);
	char *user = r->user;
	int m = r->method_number;
	int rv;
	register int x;
	const char *t;
	const apr_array_header_t *reqs_arr = ap_requires(r);
	require_line *reqs;

	/* use MySQL auth only if we have a database */
	if (!auth_db_name && !sec->db_name) {
		return DECLINED;
	}

	/* What do we do if there's no requires line available?  Either say
	 * "bad puppy" if we're king shit, or say "not my problem" otherwise.
	 */
	if (!reqs_arr) {
		if (sec->authoritative) {
			APACHELOG(APLOG_ERR, r, "No requires line available");
			return HTTP_UNAUTHORIZED;
		} else {
			return DECLINED;
		}
	}

	/* This is an array of all the requires lines which apply to us.
	 * There may be several, as in the case of something like:
	 * require user foo bar
	 * require group wombat
	 * That is, the user either has to belong to the group 'wombat' or
	 * be 'foo' or 'bar'.
	 * We have to check them all.  Yuck.
	 */
	reqs = (require_line *) reqs_arr->elts;

	for (x = 0; x < reqs_arr->nelts; x++) {
		/* mjp: WTF is this? */
		if (!(reqs[x].method_mask & (1 << m))) {
			continue;
		}

		t = reqs[x].requirement;

		/* OK, this might seem a little weird.  The logic is that,
		 * if the user is approved, that's sufficient, so we can
		 * return OK straight away.  Alternately, if there's an
		 * error, we bomb the check and die.  The only circumstance
		 * where we continue looping is when the user didn't pass this
		 * check, but might pass a future one, so keep looking.
		 */
		if ((rv = check_mysql_authnz_require(user, t, r))
			!= HTTP_UNAUTHORIZED)
		{
			return rv;
		}
	}

	/* We don't know, and we don't really care */
	if (!(sec->authoritative)) {
		return DECLINED;
	}

	ap_note_basic_authnz_failure(r);
	return HTTP_UNAUTHORIZED;
}

static const authn_provider authn_mysql_provider =
{
    &authnz_mysql_check_password,
    NULL
};

static void register_hooks(apr_pool_t *p)
{
	static const char * const aszPost[]={ "mod_authz_user.c", NULL };
	ap_register_provider(p, AUTHN_PROVIDER_GROUP, "mysql", "0", &authn_mysql_provider);
	ap_hook_authnz_checker(authnz_mysql_check_user_access, NULL, aszPost, APR_HOOK_MIDDLE);
}

module AP_MODULE_DECLARE_DATA authnz_mysql_module =
{
STANDARD20_MODULE_STUFF,
create_authnz_mysql_dir_config, /* dir config creater */
NULL,                       /* dir merger --- default is to override */
NULL,                       /* server config */
NULL,                       /* merge server config */
authnz_mysql_cmds,              /* command apr_table_t */
register_hooks              /* register hooks */
};
