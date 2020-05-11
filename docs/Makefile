DOCS=index Papers Presentations AdjointFinder
HDOCS=$(addsuffix .html, $(DOCS))
PHDOCS=$(addprefix html/, $(HDOCS))

.PHONY : docs
docs : $(HDOCS)

.PHONY : update
update : $(PHDOCS)
	@echo -n 'Copying to server...'
	# insert code for copying to server here.
	@echo ' done.'

%.html : jemdocs/%.jemdoc MENU
	python2.7 jemdoc.py -c bibover.conf -o $@ $< 

.PHONY : clean
clean :
	-rm -f *.html

