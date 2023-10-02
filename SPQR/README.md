# Dependencies of miniBASIS

## SuiteSparse 

The external software SuiteSparseQR, within [SuiteSparse](https://github.com/DrTimothyAldenDavis/SuiteSparse), is used in part of miniBASIS to decompose the sparse matrices containing the relations between different monomials in the Lagrangian. It is written in C++. Below you can find some recommendations for its installation.

This is needed to run the Examples in version 0. For other calculations with miniBASIS, this dependency may not be essential. In particular, one can find the corresponding functions written in Mathematica of
 - getRank, as getRankMathematica.
 - getMinimalBasis, as (future) getMinimalBasisMathematica;

It is recommended to obtain the relation matrix before configuring SuiteSparse. From 20k x 20k matrices, and on a regular computer, this dependency is probably needed.

 The scripts in C++ that make use of the SPQR libraries are 
 - SPQR/decQR.cpp performs the QR decomposition of the relation matrix, returning the diagonal elements of the upper triangular matrix R
 - SPQR/rankQR.cpp performs the QR decomposition of the relation matrix in a very fast way, returning the rank of the matrix




### INSTALLATION of SuiteSparse (including the dependencies I needed):

 - 1. Download and extract tar.gz from https://github.com/DrTimothyAldenDavis/SuiteSparse/releases/tag/v7.0.1

 - 2. Terminal
 
 ```
    cd SuiteSparse
    sudo apt-get install libopenblas-dev
    sudo apt-get install libgmp-dev
    sudo apt-get install libmpfr-dev
    make
    sudo make install
 ```
 
 - 3. Include cholmod libraries in LD_LIBRARY_PATH: Add to ~.bashrc,

 ```
    export LD_LIBRARY_PATH="user/path/SuiteSparse-7.0.1/CHOLMOD/build/":$LD_LIBRARY_PATH
    export LD_LIBRARY_PATH="/user/path/SuiteSparse-7.0.1/lib:$LD_LIBRARY_PATH"
 ```


### TEST SuiteSparse C++ implementation

 ```
    g++ decQR.cpp -lcholmod -lspqr -lsuitesparseconfig -o tmp; ./tmp matrices/mat.mtx 
    g++ decQR.cpp -lcholmod -lspqr -lsuitesparseconfig -o tmp; ./tmp matrices/matBig.mtx 
    g++ rankQR.cpp -lcholmod -lspqr -lsuitesparseconfig -o tmp; ./tmp matrices/matBig.mtx 
 ```
 
### TEST SuiteSparse in miniBASIS

Use function getMinimalBasis and getRank. But probably you want to advance in your computation before deciding if you need this 


