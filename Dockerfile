FROM ocaml/opam:alpine-3.5_ocaml-4.04.2
ENV HOME=/home/opam
WORKDIR $HOME
COPY --chown=opam:nogroup lem lem
COPY tests tests
COPY --chown=opam:nogroup tester tester
COPY Makefile .
RUN mkdir bin
ENV PATH=$PATH:$HOME/bin
RUN sudo apk update && sudo apk add m4 perl gmp-dev
# ocamlbuild and depext are already part of ocaml/opam
RUN opam install -y ocamlfind batteries yojson bignum easy-format bisect_ppx zarith sha rlp
# install lem
RUN git clone https://github.com/rems-project/lem lem-src
WORKDIR $HOME/lem-src
RUN opam config exec -- make
RUN cp lem $HOME/bin
ENV LEMLIB=$HOME/lem-src/library
# install ECC ocaml
RUN git clone https://github.com/mrsmkl/ECC-OCaml.git $HOME/ecc-ocaml
WORKDIR $HOME/ecc-ocaml/src
RUN opam config exec -- make depend
RUN opam config exec -- make
RUN opam config exec -- make install
WORKDIR $HOME
# install secp256k1
RUN git clone https://github.com/bitcoin/secp256k1 $HOME/secp256k1
WORKDIR $HOME/secp256k1
RUN sudo apk update && sudo apk add autoconf automake libtool
RUN ./autogen.sh
RUN ./configure --enable-module-recovery
RUN make
RUN sudo make install
# install secp256k1 ocaml wrapper
WORKDIR $HOME
ADD --chown=opam:nogroup https://github.com/dakk/secp256k1-ml/archive/0.4.0.tar.gz .
RUN tar xf 0.4.0.tar.gz
WORKDIR $HOME/secp256k1-ml-0.4.0
RUN opam pin add secp256k1 . -n
RUN opam lint secp256k1.opam
RUN opam install -y secp256k1 --deps-only
RUN opam install -y secp256k1 "-v"
# run the tests
WORKDIR $HOME/tester
RUN chmod a+x ./compile.sh
RUN eval `opam config env` && ./compile.sh

