#!/bin/sh -e

rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Alignment.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Divisible.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Binary.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/Tags.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/FileFormat.v
rocq compile -Q src/main/coq com.io7m.entomos src/main/coq/ExampleFileFormat.v

./rocq-doc.sh
