#!/bin/bash
# Usage: ./compile_chapter.sh chapters/g01_foundations.tex
# Compiles main.tex after replacing the chapter section
# This is a NO-OP — agents should just compile main.tex after editing it
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode -halt-on-error main.tex > /tmp/pdflatex_chapter_test.log 2>&1
RESULT=$?
if [ $RESULT -ne 0 ]; then
    echo "FAILED — last 20 lines:"
    tail -20 /tmp/pdflatex_chapter_test.log
else
    echo "OK"
fi
exit $RESULT
