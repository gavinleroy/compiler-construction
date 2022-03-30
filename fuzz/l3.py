#!/usr/bin/env python3

from fuzzingbook.Grammars import *

L3_GRAMMAR = {
    "<start>" : ["<program><expr>", "<expr>"],
    "<program>" : ["<def>", "<defrec>"],
    "<def>" : ["(def <ident> <expr>)"],
    "<defrec>" : ["(defrec <ident> <fun>)"],
    "<expr>" : [], # TODO

}
