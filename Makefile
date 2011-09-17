APXS2	= /usr/bin/apxs2
APXS2FLAGS =
SRCS	= mod_authnz_mysql.c
HDRS	= config.h
OPTS	= -I/usr/include/mysql -L/usr/lib -lmysqlclient
MODULES = mod_authnz_mysql.so

all: $(MODULES)

mod_authnz_mysql.so: mod_authnz_mysql.la
	cp .libs/mod_authnz_mysql.so .

mod_authnz_mysql.la: $(SRCS) $(HDRS)
	$(APXS2) $(APXS2FLAGS) -o $@ $(OPTS) -DAPACHE2 -c $(SRCS)

clean:
	-rm -rf *.o *.so *.lo *.slo *.la .libs

distclean: clean
	-rm -f config.status config.log config.h Makefile
	-rm -rf autom4te.cache

maintclean: distclean
	-rm -f configure
