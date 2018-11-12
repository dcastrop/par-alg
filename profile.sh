#!/bin/bash

# stack --work-dir .stack-work-profile clean
stack --work-dir .stack-work-profile --profile build --ghc-options="-ddump-stg -ddump-to-file"

stack exec --work-dir .stack-work-profile -- par-lang $2 +RTS $1 -p

hp2ps par-lang.hp -e8in -c
