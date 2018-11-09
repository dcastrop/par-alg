#!/bin/bash

stack --work-dir .stack-work-profile clean
stack --work-dir .stack-work-profile --profile build --ghc-options="-ddump-stg -ddump-to-file"

stack exec --work-dir .stack-work-profile -- par-lang --recursion-depth=$2 $3 +RTS $1 -p
