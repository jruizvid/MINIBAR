// many lines taken from example.cpp
#include "SuiteSparseQR.hpp"
#include "SuiteSparse_config.h"
#include <string>

int main (int argc, char **argv)
{
    cholmod_common Common, *cc;
    cholmod_sparse *A;

    // start the engines of CHOLMOD
    cc = &Common;
    cholmod_l_start (cc);

    // declare output file
    FILE* fout;

    // load relation matrix A (saved by the MMA notebook in the filePath given as argument)
    int mtype ;
    const char* filePath = argv[1];
    FILE* fp; fp = fopen(filePath, "r"); 
    //FILE* fp; fp = fopen("/home/joanruiz/Programs/SuiteSparse-7.0.1/SPQR/Matrix/b1_ss.mtx", "r");     
    A = (cholmod_sparse *) cholmod_l_read_matrix (fp, 1, &mtype, cc) ;
    fclose(fp);

    // Gaussian Elimination
    cholmod_sparse *R, *H;
    int64_t *E;
    int64_t *rowPermH;
            
    SuiteSparseQR  <double>
    (
        3,         // ordering of columns & rows: 0 fails; 1 singletons only; 3 keeps matrix unchanged (respects our order of opes; slow); SPQR_ORDERING_DEFAULT just to get the nbr of opes, not the basis, 3x faster
        SPQR_DEFAULT_TOL,         // only accept singletons above tol
        std::max(A->nrow,A->ncol),                  // number of rows of C and R to return
        A,                        // m-by-n sparse matrix
                   // outputs
        &R,        // the R factor
        &E,        // permutation of 0:n-1, NULL if identity
        &H,        // the Householder vectors (m-by-nh)
        &rowPermH, // size m; row permutation for H
        NULL,      // size nh, Householder coefficients
        cc         // workspace and parameters
    ) ;

    // prepare path to save matrix file
    std::string tmppath = std::string(filePath);
    size_t lastSlashIndex = tmppath.find_last_of('/');
    tmppath = tmppath.substr(0, lastSlashIndex + 1);

    // get diagonal of R
    cholmod_sparse *D;
    D = cholmod_l_band (R,0,0,1,cc);
    
    // print info
    cholmod_l_print_sparse(R,"R",cc); 
    cholmod_l_print_sparse(D,"D",cc); 
    
    // save D
    fout = fopen((tmppath + std::string("matOutD.mtx")).c_str(), "w");
    cholmod_l_write_sparse(fout,D,NULL,NULL,cc);
    fclose(fout);
    
    // save R
    fout = fopen((tmppath + std::string("matOutR.mtx")).c_str(), "w");
    cholmod_l_write_sparse(fout,R,NULL,NULL,cc);
    fclose(fout);

    // save vector of permutations
    fout = fopen((tmppath + std::string("permOut.txt")).c_str(), "w");
    for (int i = 0; i < (int)A->ncol; i++) { fprintf(fout, "%ld ", E[i]); }
    fclose(fout);
    
    // print rank that will be retrieved by MMA
    printf("Rank:  %10ld",cc->SPQR_istat [4]); //use 10 characters

    // free everything and finish CHOLMOD
    cholmod_l_free_sparse (&A, cc);
    cholmod_l_free_sparse (&R, cc);
    cholmod_l_free_sparse (&D, cc);
    cholmod_l_finish (cc);
    
    return 0;
}
