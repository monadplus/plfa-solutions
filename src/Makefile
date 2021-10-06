# https://stackoverflow.com/questions/16924333/makefile-compiling-from-directory-to-another-directory

.PHONY : clean

AGDA=agda
SOURCEDIR=plfa/*
SOURCES = $(wildcard $(SOURCEDIR)/*.agda)

all: compile

compile: $(SOURCES)
	xargs $(AGDA) -v 2 $<

html: $(SOURCES)
	xargs $(AGDA) --html --html-dir=html $<

clean:
	rm -f $(SOURCEDIR)/*.agdai
