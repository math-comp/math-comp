# porting.tex assumes the preliminary installation of https://github.com/affeldt-aist/ssrmint
# see the README for installation instructions
FILE = porting
TEX = pdflatex --shell-escape

all:
	$(TEX) $(FILE).tex
	bibtex $(FILE)
	$(TEX) $(FILE).tex
