#!/bin/bash

apalache-mc check \
        --no-deadlock \
		--debug=true \
        --inv=Inv \
		--nworkers=4 \
		--length=20 \
        MC.tla $@
