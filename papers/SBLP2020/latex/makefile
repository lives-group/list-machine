target: all

all: 
	pdflatex paper.tex
	bibtex paper.aux
	pdflatex paper.tex
	pdflatex paper.tex

clean: 
	rm *.bbl *.aux *.log *.ptb *.blg
