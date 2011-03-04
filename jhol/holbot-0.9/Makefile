# $Id: Makefile,v 1.4 2007/06/29 21:43:21 rjones Exp $

include Makefile.config

all:    holbot.pl


holbot.pl: holbot.pl.in Makefile.config Makefile
	sed \
	  -e 's|@WRAPPER@|$(WRAPPER)|' \
	  -e 's|@VERSION@|$(VERSION)|' \
	  -e 's|@PACKAGE@|$(PACKAGE)|' \
	  < $< > $@
	chmod 0755 $@


test check:
	perl -Tc holbot.pl




.PHONY:	depend dist check-manifest dpkg doc print_test


