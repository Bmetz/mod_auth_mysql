# Process this file with autoconf to produce a configure script.
AC_INIT(mod_authnz_mysql, 1.0)

AC_CONFIG_SRCDIR([mod_authnz_mysql.c])
AM_INIT_AUTOMAKE
AC_CONFIG_HEADER([config.h])


# Checks for programs.

# Checks for libraries.
AC_CHECK_LIB([mysqlclient], [mysql_init])

modules="mod_authnz_mysql.so"
AC_SUBST(modules)

AC_ARG_WITH(apxs2,
AC_HELP_STRING([--with-apxs2], [location of the apxs2 Apache2 module helper]),
[
	if test ! -x $withval; then
		AC_MSG_ERROR($withval not found)
	else
		apxs2="$withval"
	fi
],
[
	# Test likely apxs2 locations
	if test -x /usr/bin/apxs2; then
		apxs2="/usr/bin/apxs2"
	elif test -x /usr/local/bin/apxs2; then
		apxs2="/usr/local/bin/apxs2"
	elif test -x /usr/sbin/apxs2; then
		apxs2="/usr/sbin/apxs2"		
	else
		AC_MSG_ERROR(Apache2 extension helper not found!)
	fi
])
AC_SUBST(apxs2)

AC_ARG_WITH(mysql-includes,
AC_HELP_STRING([--with-mysql-includes], [MySQL includes directory]),
[
if test ! -e $withval/mysql.h; then
	AC_MSG_ERROR(Invalid MySQL includes directory: $withval)
else
	mysql_includes="-I$withval"
fi
],
[
# Common location finder
if test -e /usr/include/mysql/mysql.h; then
	mysql_includes="-I/usr/include/mysql"
elif test -e /usr/include/mysql.h; then
	mysql_includes="-I/usr/include"
elif test -e /usr/local/include/mysql/mysql.h; then
	mysql_includes="-I/usr/local/include/mysql"
elif test -e /usr/local/include/mysql.h; then
	mysql_includes="-I/usr/local/include"
else
	AC_MSG_ERROR(MySQL include files not found!)
fi
])
AC_SUBST(mysql_includes)

AC_ARG_WITH(mysql-libs,
AC_HELP_STRING([--with-mysql-libs], [MySQL libraries directory]),
[
if test ! -e $withval/libmysqlclient.so; then
	AC_MSG_ERROR(Invalid MySQL libs directory: $withval)
else
	mysql_libs="-L$withval"
fi
],
[
# Common location finder
if test -e /usr/lib/mysql/libmysqlclient.so; then
	mysql_libs="-L/usr/lib/mysql"
elif test -e /usr/lib/libmysqlclient.so; then
	mysql_libs="-L/usr/lib"
elif test -e /usr/local/lib/mysql/libmysqlclient.so; then
	mysql_libs="-L/usr/local/lib/mysql"
elif test -e /usr/local/lib/libmysqlclient.so ; then
	mysql_libs="-L/usr/local/lib"
else
	AC_MSG_ERROR(MySQL libraries not found!)
fi
])
AC_SUBST(mysql_libs)

AC_SUBST(build_opts, "$mysql_includes $mysql_libs")

# Checks for header files.
AC_CHECK_HEADERS([crypt.h])

AC_CHECK_LIB([crypt], [crypt])

if test -n $HAVE_CRYPT_H; then
	AC_TRY_RUN(
[
#include <crypt.h>
#include <string.h>

int main()
{
	return strcmp(crypt("a", "\$1\$aaaaaaaa"),
			"\$1\$aaaaaaaa\$S270EsVIz5M8Y9/k4SSEf.");
}
],
AC_DEFINE(CRYPT_MD5, 1, [Enable crypt() MD5 encryption]),
,,)
	AC_TRY_RUN(
[
#include <crypt.h>
#include <string.h>

int main()
{
	return strcmp(crypt("a", "aa"),
			"aafKPWZb/dLAs");
}
],
AC_DEFINE(CRYPT_DES, 1, [Enable DES encrpytion]),
,,)

fi  # if test -n HAVE_CRYPT_H

# Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST

# Checks for library functions.
AC_TYPE_SIGNAL

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
