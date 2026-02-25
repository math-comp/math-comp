#!/bin/sh
DST=$2
$1 top -Q . mathcomp <<EOF
From HB Require Import structures.
From mathcomp Require Import all.
HB.graph "$DST".
EOF
