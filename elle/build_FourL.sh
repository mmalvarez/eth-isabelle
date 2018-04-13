#!/bin/bash
ocamlc nums.cma unix.cma ./FourLShim.ml generated/FourL.ml -o fourlc
