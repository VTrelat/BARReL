$pdf_mode = 1;
$pdflatex = 'pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -synctex=1 %O %S';
$bibtex_use = 2;
$out_dir = 'build';
$max_repeat = 5;
@default_files = ('main.tex');
