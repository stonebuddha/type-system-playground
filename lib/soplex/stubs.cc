#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>
#include <soplex.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

using namespace soplex;

#define Mpq_val(v) ((__mpq_struct *) Data_custom_val(v))

static void camlidl_custom_mpq_finalize(value val) {
    __mpq_struct* mpq = Mpq_val(val);
    mpq_clear(mpq);
}

static int camlidl_custom_mpq_compare(value val1, value val2) {
    int res;
    __mpq_struct* mpq1;
    __mpq_struct* mpq2;

    mpq1 = Mpq_val(val1);
    mpq1 = Mpq_val(val2);
    res = mpq_cmp(mpq1, mpq2);
    res = res > 0 ? 1 : res == 0 ? 0 : -1;

    return res;
}

static long camlidl_custom_mpq_hash(value val) {
    __mpq_struct* mpq = Mpq_val(val);
    unsigned long num = mpz_get_ui(mpq_numref(mpq));
    unsigned long den = mpz_get_ui(mpq_denref(mpq));
    long hash;
    if (num == 0) hash = 0;
    else if (den == 0) hash = num > 0 ? LONG_MAX : LONG_MIN;
    else hash = (num < den ? den / num : num / den);
    return hash;
}

static struct custom_operations camlidl_custom_mpq = {
    "stonebuddha.camlidl_gmp_mpq.0",
    camlidl_custom_mpq_finalize,
    camlidl_custom_mpq_compare,
    camlidl_custom_mpq_hash,
    custom_serialize_default,
    custom_deserialize_default,
    custom_compare_ext_default
};

static value camlidl_mpq_ptr_c2ml(const __mpq_struct *mpq) {
    value val;

    val = caml_alloc_custom(&camlidl_custom_mpq, sizeof(__mpq_struct), 0, 1);
    mpq_init(Mpq_val(val));
    mpq_set(Mpq_val(val), mpq);

    return val;
}

#define Model_val(v) (*((SoPlex **) Data_custom_val(v)))

static void finalize_model(value v) {
    delete Model_val(v);
}

static struct custom_operations soplex_model_ops = {
    "stonebuddha.ocaml-soplex.0",
    finalize_model,
    custom_compare_default,
    custom_hash_default,
    custom_serialize_default,
    custom_deserialize_default
};

static value alloc_model(SoPlex *c_model) {
    value block = caml_alloc_custom(&soplex_model_ops, sizeof(SoPlex *), 0, 1);
    Model_val(block) = c_model;
    return block;
}

static double robust_mpq_get_d(const __mpq_struct *mpq) {
    __mpz_struct num, den;
    mpz_inits(&num, &den, NULL);
    mpq_get_num(&num, mpq);
    mpq_get_den(&den, mpq);
    if (mpz_sgn(&num) > 0 && mpz_sgn(&den) == 0) {
        mpz_clears(&num, &den, NULL);
        return INFINITY;
    } else if (mpz_sgn(&num) < 0 && mpz_sgn(&den) == 0) {
        mpz_clears(&num, &den, NULL);
        return -INFINITY;
    } else {
        mpz_clears(&num, &den, NULL);
        return mpq_get_d(mpq);
    }
}

extern "C" {

/*
 * Creating model
 */

/*
 * val create : unit -> t
 */
CAMLprim value soplex_create(value unit) {
    CAMLparam1(unit);

    SoPlex *c_model = new SoPlex();
    c_model->setIntParam(SoPlex::SYNCMODE, 2);
    c_model->setIntParam(SoPlex::READMODE, 1);
    c_model->setIntParam(SoPlex::SOLVEMODE, 2);
    c_model->setIntParam(SoPlex::CHECKMODE, 2);
    c_model->setRealParam(SoPlex::FEASTOL, 0.0);
    c_model->setRealParam(SoPlex::OPTTOL, 0.0);

    CAMLreturn(alloc_model(c_model));
}

/*
 * Getters and setters of problem parameters
 */

/*
 * val number_rows : t -> int
 */
CAMLprim value soplex_number_rows(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_num_rows = c_model->numRowsRational();

    CAMLreturn(Val_int(c_num_rows));
}

/*
 * val number_columns : t -> int
 */
CAMLprim value soplex_number_columns(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_num_columns = c_model->numColsRational();

    CAMLreturn(Val_int(c_num_columns));
}

/*
 * val number_elements : t -> int
 */
CAMLprim value soplex_number_elements(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_num_elements = c_model->numNonzerosRational();

    CAMLreturn(Val_int(c_num_elements));
}

/*
 * val direction : t -> direction
 */
CAMLprim value soplex_direction(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_direction = c_model->intParam(SoPlex::OBJSENSE);
    c_direction = c_direction == SoPlex::OBJSENSE_MAXIMIZE ? 0 : 1;

    CAMLreturn(Val_int(c_direction));
}

/*
 * val set_direction : t -> direction -> unit
 */
CAMLprim value soplex_set_direction(value model, value direction) {
    CAMLparam2(model, direction);

    SoPlex *c_model = Model_val(model);
    int c_direction = Int_val(direction) == 0 ? SoPlex::OBJSENSE_MAXIMIZE : SoPlex::OBJSENSE_MINIMIZE;
    c_model->setIntParam(SoPlex::OBJSENSE, c_direction);

    CAMLreturn(Val_unit);
}

/*
 * val add_rows : t -> row array -> int -> unit
 */
CAMLprim value soplex_add_rows(value model, value rows, value nrows) {
    CAMLparam3(model, rows, nrows);
    CAMLlocal3(row, elements, element);

    SoPlex *c_model = Model_val(model);
    const int c_row_count = Int_val(nrows);
    LPRowSetRational c_row_set(c_row_count);
    LPRowSet c_row_set_flt(c_row_count);
    int i, j, c_row_size;

    __mpq_struct c_coef[1], c_lb[1], c_rb[1];
    mpq_inits(&c_coef[0], &c_lb[0], &c_rb[0], NULL);
    for (i = 0; i < c_row_count; ++i) {
        row = Field(rows, i);
        elements = Field(row, 2);
        c_row_size = Wosize_val(elements);
        DSVectorRational vec(c_row_size);
        DSVector vec_flt(c_row_size);
        for (j = 0; j < c_row_size; ++j) {
            element = Field(elements, j);
            mpq_set(&c_coef[0], Mpq_val(Field(element, 1)));
            vec.add(Int_val(Field(element, 0)), c_coef);
            vec_flt.add(Int_val(Field(element, 0)), robust_mpq_get_d(c_coef));
        }
        mpq_set(&c_lb[0], Mpq_val(Field(row, 0)));
        mpq_set(&c_rb[0], Mpq_val(Field(row, 1)));
        c_row_set.add(LPRowRational(c_lb, vec, c_rb));
        c_row_set_flt.add(LPRow(robust_mpq_get_d(c_lb), vec_flt, robust_mpq_get_d(c_rb)));
    }
    mpq_clears(&c_coef[0], &c_lb[0], &c_rb[0], NULL);

    c_model->addRowsRational(c_row_set);
    c_model->addRowsReal(c_row_set_flt);

    CAMLreturn(Val_unit);
}

/*
 * val delete_rows : t -> int array -> unit
 */
CAMLprim value soplex_delete_rows(value model, value which) {
    CAMLparam2(model, which);

    SoPlex *c_model = Model_val(model);
    const int c_number = Wosize_val(which);
    int *c_which = new int[c_number];
    int i;

    for (i = 0; i < c_number; ++i) {
        c_which[i] = Int_val(Field(which, i));
    }
    c_model->removeRowsRational(c_which, c_number);
    c_model->removeRowsReal(c_which, c_number);
    delete[] c_which;

    CAMLreturn(Val_unit);
}

/*
 * val add_columns : t -> column array -> int -> unit
 */
CAMLprim value soplex_add_columns(value model, value columns, value ncolumns) {
    CAMLparam3(model, columns, ncolumns);
    CAMLlocal3(column, elements, element);

    SoPlex *c_model = Model_val(model);
    const int c_column_count = Int_val(ncolumns);
    LPColSetRational c_col_set(c_column_count);
    LPColSet c_col_set_flt(c_column_count);
    int i, j, c_column_size;

    __mpq_struct c_coef[1], c_obj[1], c_lb[1], c_rb[1];
    mpq_inits(&c_coef[0], &c_obj[0], &c_lb[0], &c_rb[0], NULL);
    for (i = 0; i < c_column_count; ++i) {
        column = Field(columns, i);
        elements = Field(column, 3);
        c_column_size = Wosize_val(elements);
        DSVectorRational vec(c_column_size);
        DSVector vec_flt(c_column_size);
        for (j = 0; j < c_column_size; ++j) {
            element = Field(elements, j);
            mpq_set(&c_coef[0], Mpq_val(Field(element, 1)));
            vec.add(Int_val(Field(element, 0)), c_coef);
            vec_flt.add(Int_val(Field(element, 0)), robust_mpq_get_d(c_coef));
        }
        mpq_set(&c_obj[0], Mpq_val(Field(column, 0)));
        mpq_set(&c_lb[0], Mpq_val(Field(column, 1)));
        mpq_set(&c_rb[0], Mpq_val(Field(column, 2)));
        c_col_set.add(LPColRational(c_obj, vec, c_rb, c_lb));
        c_col_set_flt.add(LPCol(robust_mpq_get_d(c_obj), vec_flt, robust_mpq_get_d(c_rb), robust_mpq_get_d(c_lb)));
    }
    mpq_clears(&c_coef[0], &c_obj[0], &c_lb[0], &c_rb[0], NULL);

    c_model->addColsRational(c_col_set);
    c_model->addColsReal(c_col_set_flt);

    CAMLreturn(Val_unit);
}

/*
 * val delete_columns : t -> int array -> unit
 */
CAMLprim value soplex_delete_columns(value model, value which) {
    CAMLparam2(model, which);

    SoPlex *c_model = Model_val(model);
    const int c_number = Wosize_val(which);
    int *c_which = new int[c_number];
    int i;

    for (i = 0; i < c_number; ++i) {
        c_which[i] = Int_val(Field(which, i));
    }
    c_model->removeColsRational(c_which, c_number);
    c_model->removeColsReal(c_which, c_number);
    delete[] c_which;

    CAMLreturn(Val_unit);
}

/*
 * val objective_coefficients : t -> Mpqf.t array
 */
CAMLprim value soplex_objective_coefficients(value model) {
    CAMLparam1(model);
    CAMLlocal1(objective_coefficients);

    SoPlex *c_model = Model_val(model);
    int c_num_columns = c_model->numColsRational();
    DVectorRational vec(c_num_columns);
    c_model->getObjRational(vec);
    int i;

    objective_coefficients = caml_alloc(c_num_columns, 0);
    for (i = 0; i < c_num_columns; ++i) {
        const mpq_t &c_ref = vec[i].backend().data();
        Store_field(objective_coefficients, i, camlidl_mpq_ptr_c2ml(c_ref));
    }

    CAMLreturn(objective_coefficients);
}

/*
 * val change_objective_coefficients : t -> Mpqf.t array -> unit
 */
CAMLprim value soplex_change_objective_coefficients(value model, value objective_coefficients) {
    CAMLparam2(model, objective_coefficients);

    SoPlex *c_model = Model_val(model);
    int c_num_columns = c_model->numColsRational();
    DVectorRational vec(c_num_columns);
    DVector vec_flt(c_num_columns);
    int i;

    __mpq_struct c_obj[1];
    mpq_init(&c_obj[0]);
    for (i = 0; i < c_num_columns; ++i) {
        mpq_set(&c_obj[0], Mpq_val(Field(objective_coefficients, i)));
        vec[i] = c_obj;
        vec_flt[i] = robust_mpq_get_d(c_obj);
    }
    mpq_clear(&c_obj[0]);
    c_model->changeObjRational(vec);
    c_model->changeObjReal(vec_flt);

    CAMLreturn(Val_unit);
}

/*
 * Getters and setters of solver parameters
 */

/*
 * val log_level : t -> int
 */
CAMLprim value soplex_log_level(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_log_level = c_model->intParam(SoPlex::VERBOSITY);

    CAMLreturn(Val_int(c_log_level));
}

/*
 * val set_log_level : t -> int -> unit
 */
CAMLprim value soplex_set_log_level(value model, value log_level) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    c_model->setIntParam(SoPlex::VERBOSITY, Int_val(log_level));

    CAMLreturn(Val_unit);
}

/*
 * Solver oprations
 */

/*
 * val solve : t -> unit
 */
CAMLprim value soplex_solve(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    c_model->optimize();

    CAMLreturn(Val_unit);
}

/*
 * Retrieving solutions
 */

/*
 * val objective_value : t -> Mpqf.t
 */
CAMLprim value soplex_objective_value(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    const mpq_t &c_ref = c_model->objValueRational().backend().data();

    CAMLreturn(camlidl_mpq_ptr_c2ml(c_ref));
}

/*
 * val primal_column_solution : t -> Mpqf.t array
 */
CAMLprim value soplex_primal_column_solution(value model) {
    CAMLparam1(model);
    CAMLlocal1(solution);

    SoPlex *c_model = Model_val(model);
    int c_num_columns = c_model->numColsRational();
    DVectorRational vec(c_num_columns);
    c_model->getPrimalRational(vec);
    int i;

    solution = caml_alloc(c_num_columns, 0);
    for (i = 0; i < c_num_columns; ++i) {
        const mpq_t &c_ref = vec[i].backend().data();
        Store_field(solution, i, camlidl_mpq_ptr_c2ml(c_ref));
    }

    CAMLreturn(solution);
}

/*
 * val status : t -> status
 */
CAMLprim value soplex_status(value model) {
    CAMLparam1(model);

    SoPlex *c_model = Model_val(model);
    int c_status = c_model->status();
    if (c_status == SPxSolverBase<Real>::OPTIMAL) {
        c_status = 0;
    } else if (c_status == SPxSolverBase<Real>::INFEASIBLE) {
        c_status = 1;
    } else if (c_status == SPxSolverBase<Real>::UNBOUNDED) {
        c_status = 2;
    } else if (c_status == SPxSolverBase<Real>::INForUNBD) {
        c_status = 3;
    } else if (c_status == SPxSolverBase<Real>::OPTIMAL_UNSCALED_VIOLATIONS) {
        c_status = 4;
    } else {
        c_status = 5;
    }

    CAMLreturn(Val_int(c_status));
}

/*
 * MPS operations
 */

/*
 * val read_mps : t -> string -> unit
 */
CAMLprim value soplex_read_mps(value model, value filename) {
    CAMLparam2(model, filename);

    SoPlex *c_model = Model_val(model);
    const char *c_filename = String_val(filename);
    c_model->readFile(c_filename);

    CAMLreturn(Val_unit);
}

/*
 * val write_mps : t -> string -> unit
 */
CAMLprim value soplex_write_mps(value model, value filename) {
    CAMLparam2(model, filename);

    SoPlex *c_model = Model_val(model);
    const char *c_filename = String_val(filename);
    c_model->writeFile(c_filename);

    CAMLreturn(Val_unit);
}

}
