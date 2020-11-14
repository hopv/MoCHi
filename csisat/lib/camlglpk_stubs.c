/*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 */

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <glpk.h>
#include <stdio.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>   

void no_output()
{
    glp_term_out(GLP_OFF);
}

value lp_create(value unit)
{
    CAMLparam1(unit);
    glp_prob* lp = glp_create_prob();
    CAMLreturn ((value)lp);
}

value lp_delete(value lp)
{
    CAMLparam1(lp);
    glp_delete_prob((glp_prob*)lp);   
    CAMLreturn (Val_unit);
}


value lp_set_maximize(value lp)
{
    CAMLparam1(lp);
    glp_set_obj_dir((glp_prob*)lp, GLP_MAX);
    CAMLreturn (Val_unit);
}

value lp_set_minimize(value lp)
{
    CAMLparam1(lp);
    glp_set_obj_dir((glp_prob*)lp, GLP_MIN);
    CAMLreturn (Val_unit);
}

value lp_add_row(value lp, value i)
{
    CAMLparam2(lp,i);
    glp_add_rows((glp_prob*)lp, Int_val(i));
    CAMLreturn (Val_unit);
}

value lp_add_col(value lp, value i)
{
    CAMLparam2(lp,i);
    glp_add_cols((glp_prob*)lp, Int_val(i));
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_free(value lp, value i)
{
    CAMLparam2(lp,i);
    glp_set_row_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_FR, 0.0, 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_lower(value lp, value i, value lo)
{
    CAMLparam3(lp,i,lo);
    glp_set_row_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_LO, Double_val(lo), 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_upper(value lp, value i, value up)
{
    CAMLparam3(lp,i,up);
    glp_set_row_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_UP, 0.0, Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_double(value lp, value i, value lo, value up)
{
    CAMLparam4(lp,i,lo,up);
    glp_set_row_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_DB, Double_val(lo), Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_row_bnd_fixed(value lp, value i, value x)
{
    CAMLparam3(lp,i,x);
    glp_set_row_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_FX, Double_val(x), Double_val(x) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_free(value lp, value i)
{
    CAMLparam2(lp,i);
    glp_set_col_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_FR, 0.0, 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_lower(value lp, value i, value lo)
{
    CAMLparam3(lp,i,lo);
    glp_set_col_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_LO, Double_val(lo), 0.0 );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_upper(value lp, value i, value up)
{
    CAMLparam3(lp,i,up);
    glp_set_col_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_UP, 0.0, Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_double(value lp, value i, value lo, value up)
{
    CAMLparam4(lp,i,lo,up);
    glp_set_col_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_DB, Double_val(lo), Double_val(up) );
    CAMLreturn (Val_unit);
}

value lp_set_col_bnd_fixed(value lp, value i, value x)
{
    CAMLparam3(lp,i,x);
    glp_set_col_bnds((glp_prob*)lp, Int_val(i) + 1, GLP_FX, Double_val(x), Double_val(x) );
    CAMLreturn (Val_unit);
}

value lp_set_obj_coef(value lp, value i, value coeff)
{
    CAMLparam3(lp,i,coeff);
    glp_set_obj_coef((glp_prob*)lp, Int_val(i) + 1, Double_val(coeff));
    CAMLreturn (Val_unit);
}

value lp_set_mat_row(value lp, value i, value len, value array)
{
    CAMLparam4(lp,i,len,array);
    int length = Int_val(len);
    int * indexes = malloc((len + 1) * sizeof(int));
    double *val =  malloc((len + 1) * sizeof(double));
    int non_zero = 0;
    int k;
    for(k = 0; k < length; ++k){
        double entry = Double_field(array, k);
        if(entry != 0){
            ++non_zero;
            indexes[non_zero] = k+1;
            val[non_zero] = entry;
        }
    }
    if(non_zero > 0){
        glp_set_mat_row((glp_prob*)lp, Int_val(i) + 1, non_zero, indexes, val);
    }
    free(indexes);
    free(val);
    CAMLreturn (Val_unit);
}

value lp_set_mat_col(value lp, value i, value len, value array)
{
    CAMLparam4(lp,i,len,array);
    int length = Int_val(len);
    int * indexes = malloc((len + 1) * sizeof(int));
    double *val =  malloc((len + 1) * sizeof(double));
    int non_zero = 0;
    int k;
    for(k = 0; k < length; ++k){
        double entry = Double_field(array, k);
        if(entry != 0){
            ++non_zero;
            indexes[non_zero] = k+1;
            val[non_zero] = entry;
        }
    }
    if(non_zero > 0){
        glp_set_mat_col((glp_prob*)lp, Int_val(i) + 1, non_zero, indexes, val);
    }
    free(indexes);
    free(val);
    CAMLreturn (Val_unit);
}


value lp_simplex(value lp, value presolve)
{
    CAMLparam2(lp,presolve);
    glp_smcp params;
    glp_init_smcp(&params);
    if(Bool_val(presolve)){
        params.presolve = GLP_ON;
    }else{
        params.presolve = GLP_OFF;
    }
    no_output();
    int status = glp_simplex((glp_prob*)lp, &params);
    value val = Val_false;
    if(status == 0){ //no error, still need to check for optimality
        val = Val_true;
    }else{
        fprintf(stderr, "failed to solve: %d\n", status);
    }
    CAMLreturn (val);
}

value lp_simplex_exact(value lp)
{
    CAMLparam1(lp);
    no_output();
    glp_simplex((glp_prob*)lp, NULL);
    int status = glp_exact((glp_prob*)lp, NULL);
    value val = Val_false;
    if(status == 0){
        val = Val_true;
    }else{
        fprintf(stderr, "failed to solve: %d\n", status);
    }
    CAMLreturn (val);
}
value lp_get_stat(value lp)
{
    CAMLparam1(lp);
    int status = glp_get_status((glp_prob*)lp);
    CAMLreturn (Val_int(status));
}


value lp_get_obj_val(value lp)
{
    CAMLparam1(lp);
    double status = glp_get_obj_val((glp_prob*)lp);
    CAMLreturn (caml_copy_double(status));
}

value lp_get_row_stat(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_row_stat((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (Val_int(status));
}

value lp_is_col_basic(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_col_stat((glp_prob*)lp, Int_val(i) + 1);
    value val = Val_false;
    if(status == GLP_BS ) {
      val = Val_true;
    }
    CAMLreturn (val);
}

value lp_is_row_basic(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_row_stat((glp_prob*)lp, Int_val(i) + 1);
    value val = Val_false;
    if(status == GLP_BS ) {
      val = Val_true;
    }
    CAMLreturn (val);
}

value lp_get_row_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_get_row_prim((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_rows_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_get_row_prim((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}


value lp_get_row_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_get_row_dual((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_rows_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_get_row_dual((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_get_col_stat(value lp, value i)
{
    CAMLparam2(lp,i);
    int status = glp_get_col_stat((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (Val_int(status));
}

value lp_get_col_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_get_col_prim((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_cols_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_get_col_prim((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_get_col_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_get_col_dual((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_get_cols_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_get_col_dual((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_interior(value lp)
{
    CAMLparam1(lp);
    no_output();
    int status = glp_interior((glp_prob*)lp, NULL);
    value val = Val_false;
    if(status == GLP_OPT){
        val = Val_true;
    }else if (status == GLP_FEAS){
        fprintf(stderr, "feasible\n");
    }else if (status == GLP_UNDEF){
        fprintf(stderr, "undefined\n");
    }else if (status == GLP_UNBND){
        fprintf(stderr, "unbounded\n");
    }else if (status == GLP_NOFEAS){
        fprintf(stderr, "no feasible solution\n");
    }else if (status == GLP_INFEAS){
        fprintf(stderr, "infeasible\n");
    }else{
        fprintf(stderr, "unknown status: %d\n", status);
    }
    CAMLreturn (val);
}

value lp_ipt_obj_val(value lp)
{
    CAMLparam1(lp);
    double status = glp_ipt_obj_val((glp_prob*)lp);
    CAMLreturn (caml_copy_double(status));
}

value lp_ipt_row_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_ipt_row_prim((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_rows_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_ipt_row_prim((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_row_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_ipt_row_dual((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_rows_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_ipt_row_dual((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_col_primal(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_ipt_col_prim((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_cols_primal(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_ipt_col_prim((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_ipt_col_dual(value lp, value i)
{
    CAMLparam2(lp,i);
    double val = glp_ipt_col_dual((glp_prob*)lp, Int_val(i) + 1);
    CAMLreturn (caml_copy_double(val));
}

value lp_ipt_cols_dual(value lp, value length, value array)
{
    CAMLparam3(lp,length,array);
    int i;
    for(i = 0; i < Int_val(length); ++i){
        double val = glp_ipt_col_dual((glp_prob*)lp, i + 1);
        Store_double_field(array, i, val);
    }
    CAMLreturn (Val_unit);
}

value lp_dump_problem(value lp)
{
    CAMLparam1(lp);
    glp_write_prob((glp_prob*)lp, 0, "lp_error.debug"); //TODO flags ??
    CAMLreturn (Val_unit);
}
