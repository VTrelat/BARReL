$bibtex_use = 1.5;
$recorder = 1;

push @extra_pdflatex_options, '-synctex=1', '-interaction=nonstopmode';
push @extra_lualatex_options, '-synctex=1', '-interaction=nonstopmode';
push @extra_xelatex_options, '-synctex=1', '-interaction=nonstopmode';

$file_line_error //= 0;
if ($file_line_error) {
    push @extra_pdflatex_options, '-file-line-error';
    push @extra_lualatex_options, '-file-line-error';
    push @extra_xelatex_options, '-file-line-error';
}

$pdf_mode = 1;

@default_files = ('main');