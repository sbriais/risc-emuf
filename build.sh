#!/bin/sh

cpp -P fast_emul.cpp > fast_emul.ml
ocamlbuild -libs bigarray main.native
