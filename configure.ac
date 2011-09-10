# Process this file with autoconf to produce a configure script.
AC_INIT(mod_auth_mysql, 4.2.0)

AC_CONFIG_SRCDIR([mod_auth_mysql.c])
AC_CONFIG_HEADER([config.h])

# Checks for programs.

# Checks for libraries.
AC_CHECK_LIB([mysqlclient], [mysql_init])

AC_ARG_ENABLE(apache13,
AC_HELP_STRING([--enable-apache13], [Indicate that the apache 1.3 module should be built]),
[
if test "x$enableval" = "xyes"; then
	buildapache13="yes"
	modules="$modules apache13_mod_auth_mysql.so"
fi
],
[
# Build the apache 1.3 module by default
buildapache13="yes"
modules="$modules apache13_mod_auth_mysql.so"
])

AC_ARG_ENABLE(apache2,
AC_HELP_STRING([--enable-apache2], [Indicate that the apache 2.0 module should be built]),
[
if test "x$enableval" = "xyes"; then
	buildapache2="yes"
	modules="$modules apache2_mod_auth_mysql.so"
fi
])
AC_SUBST(modules)

AC_ARG_WITH(apxs,
AC_HELP_STRING([--with-apxs], [location of the apxs module helper]),
[
if test "x$buildapache13" = "xyes"; then
	if test ! -x $withval; then
		AC_MSG_ERROR($withval not found)
	else
		apxs="$withval"
	fi
fi
],
[
if test "x$buildapache13" = "xyes"; then
	# Test common apxs locations; add any others I've missed here
	if test -x /usr/bin/apxs; then
		apxs="/usr/bin/apxs"
	elif test -x /usr/local/bin/apxs; then
		apxs="/usr/local/bin/apxs"
	else
		AC_MSG_ERROR(Apache extension helper apxs not found!)
	fi
fi
])
AC_SUBST(apxs)

AC_ARG_WITH(apxs2,
AC_HELP_STRING([--with-apxs2], [location of the apxs2 Apache2 module helper]),
[
if test "x$buildapache2" = "xyes"; then
	if test ! -x $withval; then
		AC_MSG_ERROR($withval not found)
	else
		apxs2="$withval"
	fi
fi
],
[
if test "x$buildapache2" = "xyes"; then
	# Test likely apxs2 locations
	if test -x /usr/bin/apxs2; then
		apxs2="/usr/bin/apxs2"
	elif test -x /usr/local/bin/apxs2; then
		apxs2="/usr/local/bin/apxs2"
	else
		AC_MSG_ERROR(Apache2 extension helper not found!)
	fi
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
