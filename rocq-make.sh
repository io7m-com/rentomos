#!/bin/sh -e

rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/Alignment.v
rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/Divisible.v
rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/Binary.v
rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/Tags.v
rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/FileFormat.v
rocq compile -Q src/main/rocq com.io7m.entomos src/main/rocq/ExampleFileFormat.v

./rocq-doc.sh
