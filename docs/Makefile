DOCS=index 
HDOCS=$(addsuffix .html, $(DOCS))
PHDOCS=$(addprefix html/, $(HDOCS))

.PHONY : docs
docs : $(PHDOCS)

.PHONY : update
update : $(PHDOCS)
	@echo -n 'Copying to server...'
	# insert code for copying to server here.
	@echo ' done.'

html/%.html : jemdocs/%.jemdoc MENU
	python2.7 jemdoc.py -c bibover.conf -o $@ $<  && cp  -a eqs/. html/eqs

.PHONY : clean
clean :
	-rm -f html/*.html

