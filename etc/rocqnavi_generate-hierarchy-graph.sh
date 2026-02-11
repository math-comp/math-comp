#!/bin/bash
DST=$1
@@#!/bin/bash
@@DST=$1
coqtop -Q . mathcomp <<EOF
From HB Require Import structures.
From mathcomp Require Import all.
HB.graph "$DST".
EOF
