#!/bin/bash
opt -strip-debug -dot-cfg -analyze $1
dot -Tpdf -o cfg.main.pdf cfg.main.dot
evince cfg.main.pdf
