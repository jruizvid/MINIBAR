// example.cpp
#include "SuiteSparseQR.hpp"
#include "SuiteSparse_config.h"
#include <string>

int main (int argc, char **argv)
{
    cholmod_common Common, *cc;
    cholmod_sparse *A;

    // start CHOLMOD
    cc = &Common;
    cholmod_l_start (cc);


    // load A
    int mtype ;
    const char* filePath = argv[1];
    FILE* fp; fp = fopen(filePath, "r"); 
//    FILE* fp; fp = fopen("/home/joanruiz/Programs/SuiteSparse-7.0.1/SPQR/Matrix/b1_ss.mtx", "r");     
    A = (cholmod_sparse *) cholmod_l_read_matrix (fp, 1, &mtype, cc) ;

    fclose(fp);
    
    // Factorization
    SuiteSparseQR_factorize <double> (SPQR_ORDERING_DEFAULT, SPQR_DEFAULT_TOL, A, cc) ;

    // print info
    cholmod_l_print_sparse(A, "A", cc);
 
//    // print rank
//    printf("Rank of A: %ld (dim: %d x %d) \n", cc->SPQR_istat [4], (int) A->nrow, (int)A->ncol);

   
   //save matrixfile
   std::string tmppath = std::string(filePath);
   size_t lastSlashIndex = tmppath.find_last_of('/');
   tmppath = tmppath.substr(0, lastSlashIndex + 1);
   
   FILE* fout; fout = fopen((tmppath + std::string("matOut.mtx")).c_str(), "w");
   cholmod_l_write_sparse(fout,A,NULL,NULL,cc);
   fclose(fout);
   
//    //print matrix
//    double* values = (double*) A->x;
//    int* rowind = (int*) A->i;
//    int* colptr = (int*) A->p;
//    int nrows = A->nrow;
//    int ncols = A->ncol;
//    int nnz = A->nzmax;

//    printf("\n\n%f, %f, %f", values[0], values[1], values[2]);
//    printf("\n\n%d, %d, %d", colptr[0], colptr[1], colptr[2]);

//    printf("\n\n%d, %d, %d", rowind[colptr[0]], rowind[colptr[1]], rowind[colptr[2]]);
//    //printf("\n\n%d, %d, %d, %d", colptr[0], colptr[1], colptr[2], colptr[3]);



    //show nonzero elements
    //printf("Matrix A (%d x %d) with %d nonzeros:\n", nrows, ncols, nnz);



              
//    //show nonzero elements
//    printf("Matrix A (%d x %d) with %d nonzeros:\n", nrows, ncols, nnz);
//    for (int j = 0; j < ncols; j++) {
//        for (int i = colptr[j]; i < colptr[j+1]; i++) {
//          int row = rowind[i];
//          double value = values[i];
//          printf("(%d, %d) = %g\n", row, j, value);
//        }
//    }      
//                    
    
    

//    //show all elements
//  for (int row = 0; row < nrows; row++) {
//    for (int col = 0; col < ncols; col++) {
//      double value = 0.0;
//      for (int k = colptr[col]; k < colptr[col+1]; k++) {
//        if (rowind[k] == row) {
//          value = values[k];
//          break;
//        }
//      }
//      printf("%g\t", value);
//    }
//    printf("\n");
//  }

  
  
  
  
    //last printf
    printf("%10ld",cc->SPQR_istat [4]); //use 10 characters

  
    // free everything and finish CHOLMOD
    cholmod_l_free_sparse (&A, cc);
    cholmod_l_finish (cc);
    
    return 0;
}
