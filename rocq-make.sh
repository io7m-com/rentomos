#!/bin/sh -e

rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Alignment.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Divisible.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Binary.v

./rocq-doc.sh
