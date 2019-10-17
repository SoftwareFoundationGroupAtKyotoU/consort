#!/usr/bin/env perl
$latex            = 'platex -synctex=1 -kanji=utf8 -halt-on-error';
$latex_silent     = 'platex -synctex=1 -kanji=utf8 -halt-on-error -interaction=batchmode';
$bibtex           = 'pbibtex';
$dvipdf           = 'dvipdfmx %O -o %D %S';
$makeindex        = 'mendex %O -o %D %S';
$max_repeat       = 5;
$pdf_mode         = 1; # generates pdf directly
$bibtex_use       = 2;

# Prevent latexmk from removing PDF after typeset.
# This enables Skim to chase the update in PDF automatically.
$pvc_view_file_via_temporary = 0;

# Use Skim as a previewer
# if linux then evince else open else ?
if ($^O eq 'MSWin32') {
    $pdf_previewer = '"C:\Program Files (x86)\SumatraPDF\SumatraPDF.exe" -reuse-instance %O %S';
  } elsif ($^O eq 'darwin') {
    $pdf_previewer = 'open -ga /Applications/Skim.app';
  } else {
    $pdf_previewer    = "open";
#    $pdf_previewer = 'xdg-open';
  }
