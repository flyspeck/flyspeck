package edu.pitt.math.jhol.core.printer;

import static edu.pitt.math.jhol.core.printer.TermPrinter.*;
import static edu.pitt.math.jhol.core.Term.*;
import static edu.pitt.math.jhol.core.TermUtils.*;
import static edu.pitt.math.jhol.core.HOLType.*;

import java.math.BigInteger;
import java.util.ArrayList;

import edu.pitt.math.jhol.caml.*;
import edu.pitt.math.jhol.core.*;
import edu.pitt.math.jhol.core.lexer.Parser;

/**
 * Data for TermPrinter
 */
public class TermPrinterData {
	private final static String the_interface = "List(Pair(String,Pair(String,HOLType)),[Pair(\"+\",Pair(\"real_add\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"-\",Pair(\"real_sub\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"*\",Pair(\"real_mul\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"/\",Pair(\"real_div\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"<\",Pair(\"real_lt\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"<=\",Pair(\"real_le\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\">\",Pair(\"real_gt\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\">=\",Pair(\"real_ge\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"--\",Pair(\"real_neg\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])));Pair(\"pow\",Pair(\"real_pow\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])])));Pair(\"inv\",Pair(\"real_inv\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])));Pair(\"abs\",Pair(\"real_abs\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])));Pair(\"max\",Pair(\"real_max\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"min\",Pair(\"real_min\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])])));Pair(\"&\",Pair(\"real_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"real\"[])])));Pair(\"mod\",Pair(\"real_mod\",Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])])));Pair(\"+\",Pair(\"+\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])));Pair(\"-\",Pair(\"-\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])));Pair(\"*\",Pair(\"*\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])])])));Pair(\"<\",Pair(\"<\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])));Pair(\"<=\",Pair(\"<=\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])));Pair(\">\",Pair(\">\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])));Pair(\">=\",Pair(\">=\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])));Pair(\"divides\",Pair(\"num_divides\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])));Pair(\"mod\",Pair(\"num_mod\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"bool\"[])])])])));Pair(\"coprime\",Pair(\"num_coprime\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"bool\"[])])));Pair(\"gcd\",Pair(\"num_gcd\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"num\"[]),Tyapp(\"num\"[])]),Tyapp(\"num\"[])])));Pair(\"vol\",Pair(\"measure\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"3\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"real\"[])])));Pair(\"NULLSET\",Pair(\"negligible\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"3\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])));Pair(\"+\",Pair(\"vector_add\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])));Pair(\"-\",Pair(\"vector_sub\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])));Pair(\"--\",Pair(\"vector_neg\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])));Pair(\"norm\",Pair(\"vector_norm\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"real\"[])])));Pair(\"**\",Pair(\"vector_matrix_mul\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"M\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])])])));Pair(\"real_segment\",Pair(\"closed_real_segment\",Tyapp(\"fun\"[Tyapp(\"list\"[Tyapp(\"prod\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"real_segment\",Pair(\"open_real_segment\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"real_interval\",Pair(\"closed_real_interval\",Tyapp(\"fun\"[Tyapp(\"list\"[Tyapp(\"prod\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])])]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"real_interval\",Pair(\"open_real_interval\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])]),Tyapp(\"fun\"[Tyapp(\"real\"[]),Tyapp(\"bool\"[])])])));Pair(\"inv\",Pair(\"complex_inv\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])));Pair(\"pow\",Pair(\"complex_pow\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])])));Pair(\"/\",Pair(\"complex_div\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])])));Pair(\"*\",Pair(\"complex_mul\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])])));Pair(\"-\",Pair(\"vector_sub\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])])));Pair(\"+\",Pair(\"vector_add\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])])));Pair(\"--\",Pair(\"vector_neg\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"2\"[])])])));Pair(\"*\",Pair(\"geom_mul\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"multivector\"[Tyvar(\"N\")])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"multivector\"[Tyvar(\"N\")])]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"multivector\"[Tyvar(\"N\")])])])])));Pair(\"segment\",Pair(\"closed_segment\",Tyapp(\"fun\"[Tyapp(\"list\"[Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188551\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188551\")])])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188551\")]),Tyapp(\"bool\"[])])])));Pair(\"segment\",Pair(\"open_segment\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188549\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188549\")])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?188549\")]),Tyapp(\"bool\"[])])])));Pair(\"interval\",Pair(\"closed_interval\",Tyapp(\"fun\"[Tyapp(\"list\"[Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182242\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182242\")])])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182242\")]),Tyapp(\"bool\"[])])])));Pair(\"interval\",Pair(\"open_interval\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182240\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182240\")])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?182240\")]),Tyapp(\"bool\"[])])])));Pair(\"**\",Pair(\"matrix_vector_mul\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"M\")])])])));Pair(\"**\",Pair(\"matrix_mul\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"P\")]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"P\")]),Tyvar(\"M\")])])])));Pair(\"-\",Pair(\"matrix_sub\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")])])])));Pair(\"+\",Pair(\"matrix_add\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")])])])));Pair(\"--\",Pair(\"matrix_neg\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")]),Tyapp(\"cart\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyvar(\"M\")])])));Pair(\"dist\",Pair(\"distance\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")]),Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"N\")])]),Tyapp(\"real\"[])])));Pair(\"gcd\",Pair(\"int_gcd\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])]),Tyapp(\"int\"[])])));Pair(\"coprime\",Pair(\"int_coprime\",Tyapp(\"fun\"[Tyapp(\"prod\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])]),Tyapp(\"bool\"[])])));Pair(\"mod\",Pair(\"int_mod\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])])));Pair(\"divides\",Pair(\"int_divides\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])));Pair(\"&\",Pair(\"int_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"int\"[])])));Pair(\"min\",Pair(\"int_min\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])])));Pair(\"max\",Pair(\"int_max\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])])));Pair(\"abs\",Pair(\"int_abs\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])));Pair(\"pow\",Pair(\"int_pow\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"int\"[])])])));Pair(\"--\",Pair(\"int_neg\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])));Pair(\">=\",Pair(\"int_ge\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])));Pair(\">\",Pair(\"int_gt\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])));Pair(\"<=\",Pair(\"int_le\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])));Pair(\"<\",Pair(\"int_lt\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"bool\"[])])])));Pair(\"*\",Pair(\"int_mul\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])])));Pair(\"-\",Pair(\"int_sub\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])])));Pair(\"+\",Pair(\"int_add\",Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"fun\"[Tyapp(\"int\"[]),Tyapp(\"int\"[])])])));Pair(\"&\",Pair(\"hreal_of_num\",Tyapp(\"fun\"[Tyapp(\"num\"[]),Tyapp(\"hreal\"[])])));Pair(\"<=>\",Pair(\"=\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])))])";
	private final static String infixes = "List(Pair(String,Pair(Int,String)),[Pair(\"<=>\",Pair(2,\"right\"));Pair(\"==>\",Pair(4,\"right\"));Pair(\"\\/\",Pair(6,\"right\"));Pair(\"/\\\",Pair(8,\"right\"));Pair(\"==\",Pair(10,\"right\"));Pair(\"===\",Pair(10,\"right\"));Pair(\"treal_eq\",Pair(10,\"right\"));Pair(\"IN\",Pair(11,\"right\"));Pair(\"belong\",Pair(11,\"right\"));Pair(\"--->\",Pair(12,\"right\"));Pair(\"-->\",Pair(12,\"right\"));Pair(\"<\",Pair(12,\"right\"));Pair(\"<<\",Pair(12,\"right\"));Pair(\"<<<\",Pair(12,\"right\"));Pair(\"<<=\",Pair(12,\"right\"));Pair(\"<=\",Pair(12,\"right\"));Pair(\"<=_c\",Pair(12,\"right\"));Pair(\"<_c\",Pair(12,\"right\"));Pair(\"=\",Pair(12,\"right\"));Pair(\"=_c\",Pair(12,\"right\"));Pair(\">\",Pair(12,\"right\"));Pair(\">=\",Pair(12,\"right\"));Pair(\">=_c\",Pair(12,\"right\"));Pair(\">_c\",Pair(12,\"right\"));Pair(\"HAS_SIZE\",Pair(12,\"right\"));Pair(\"PSUBSET\",Pair(12,\"right\"));Pair(\"SUBSET\",Pair(12,\"right\"));Pair(\"absolutely_integrable_on\",Pair(12,\"right\"));Pair(\"absolutely_real_integrable_on\",Pair(12,\"right\"));Pair(\"analytic_on\",Pair(12,\"right\"));Pair(\"complex_differentiable\",Pair(12,\"right\"));Pair(\"continuous\",Pair(12,\"right\"));Pair(\"continuous_on\",Pair(12,\"right\"));Pair(\"convex_on\",Pair(12,\"right\"));Pair(\"differentiable\",Pair(12,\"right\"));Pair(\"differentiable_on\",Pair(12,\"right\"));Pair(\"divides\",Pair(12,\"right\"));Pair(\"division_of\",Pair(12,\"right\"));Pair(\"edge_of\",Pair(12,\"right\"));Pair(\"exposed_face_of\",Pair(12,\"right\"));Pair(\"extreme_point_of\",Pair(12,\"right\"));Pair(\"face_of\",Pair(12,\"right\"));Pair(\"facet_of\",Pair(12,\"right\"));Pair(\"fine\",Pair(12,\"right\"));Pair(\"has_complex_derivative\",Pair(12,\"right\"));Pair(\"has_derivative\",Pair(12,\"right\"));Pair(\"has_integral\",Pair(12,\"right\"));Pair(\"has_integral_compact_interval\",Pair(12,\"right\"));Pair(\"has_measure\",Pair(12,\"right\"));Pair(\"has_real_derivative\",Pair(12,\"right\"));Pair(\"has_real_integral\",Pair(12,\"right\"));Pair(\"has_real_measure\",Pair(12,\"right\"));Pair(\"has_vector_derivative\",Pair(12,\"right\"));Pair(\"holomorphic_on\",Pair(12,\"right\"));Pair(\"homeomorphic\",Pair(12,\"right\"));Pair(\"inseg\",Pair(12,\"right\"));Pair(\"integrable_on\",Pair(12,\"right\"));Pair(\"limit_point_of\",Pair(12,\"right\"));Pair(\"multivector\",Pair(12,\"right\"));Pair(\"permutes\",Pair(12,\"right\"));Pair(\"polar_cycle_on\",Pair(12,\"right\"));Pair(\"polar_le\",Pair(12,\"right\"));Pair(\"polar_lt\",Pair(12,\"right\"));Pair(\"re_eqvl\",Pair(12,\"right\"));Pair(\"real_continuous\",Pair(12,\"right\"));Pair(\"real_continuous_on\",Pair(12,\"right\"));Pair(\"real_convex_on\",Pair(12,\"right\"));Pair(\"real_differentiable\",Pair(12,\"right\"));Pair(\"real_differentiable_on\",Pair(12,\"right\"));Pair(\"real_integrable_on\",Pair(12,\"right\"));Pair(\"real_sums\",Pair(12,\"right\"));Pair(\"real_uniformly_continuous_on\",Pair(12,\"right\"));Pair(\"retract_of\",Pair(12,\"right\"));Pair(\"simplex\",Pair(12,\"right\"));Pair(\"sums\",Pair(12,\"right\"));Pair(\"tagged_division_of\",Pair(12,\"right\"));Pair(\"tagged_partial_division_of\",Pair(12,\"right\"));Pair(\"treal_le\",Pair(12,\"right\"));Pair(\"uniformly_continuous_on\",Pair(12,\"right\"));Pair(\",\",Pair(14,\"right\"));Pair(\"in_direction\",Pair(14,\"right\"));Pair(\"within\",Pair(14,\"right\"));Pair(\"..\",Pair(15,\"right\"));Pair(\"+\",Pair(16,\"right\"));Pair(\"++\",Pair(16,\"right\"));Pair(\"+_c\",Pair(16,\"right\"));Pair(\"UNION\",Pair(16,\"right\"));Pair(\"treal_add\",Pair(16,\"right\"));Pair(\"-\",Pair(18,\"left\"));Pair(\"DIFF\",Pair(18,\"left\"));Pair(\"*\",Pair(20,\"right\"));Pair(\"**\",Pair(20,\"right\"));Pair(\"*_c\",Pair(20,\"right\"));Pair(\"INTER\",Pair(20,\"right\"));Pair(\"cross\",Pair(20,\"right\"));Pair(\"dot\",Pair(20,\"right\"));Pair(\"inner\",Pair(20,\"right\"));Pair(\"outer\",Pair(20,\"right\"));Pair(\"treal_mul\",Pair(20,\"right\"));Pair(\"%\",Pair(21,\"right\"));Pair(\"INSERT\",Pair(21,\"right\"));Pair(\"DELETE\",Pair(21,\"left\"));Pair(\"hull\",Pair(21,\"left\"));Pair(\"CROSS\",Pair(22,\"right\"));Pair(\"grade\",Pair(22,\"right\"));Pair(\"/\",Pair(22,\"left\"));Pair(\"DIV\",Pair(22,\"left\"));Pair(\"MOD\",Pair(22,\"left\"));Pair(\"div\",Pair(22,\"left\"));Pair(\"rem\",Pair(22,\"left\"));Pair(\"POWER\",Pair(24,\"right\"));Pair(\"iso\",Pair(24,\"right\"));Pair(\"EXP\",Pair(24,\"left\"));Pair(\"cpow\",Pair(24,\"left\"));Pair(\"pow\",Pair(24,\"left\"));Pair(\"$\",Pair(25,\"left\"));Pair(\"$$\",Pair(25,\"left\"));Pair(\"o\",Pair(26,\"right\"))])";
	private final static String prefixes = "List(String,[\"~\";\"--\";\"mod\"])";
	private final static String binders = "List(String,[\"\\\";\"!\";\"?\";\"?!\";\"@\";\"minimal\";\"lambda\";\"lambdas\"])";

	public static void init() {
		try {
			initMisc();
			initInfixes();
			initPrefixes();
			initBinders();
			initInterface();
			initSpecialPrinters();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	/**
	 * initMisc()
	 */
	public static void initMisc() {
		addUnspacedBinop(",");
		addUnspacedBinop("..");
		addUnspacedBinop("$");
	}

	/**
	 * initInfixes()
	 */
	public static void initInfixes() throws Exception {
		/*
		 * parse_as_infix("<=>", 2, InfixAssoc.RIGHT); parse_as_infix("==>", 4,
		 * InfixAssoc.RIGHT); parse_as_infix("\\/", 6, InfixAssoc.RIGHT);
		 * parse_as_infix("/\\", 8, InfixAssoc.RIGHT); parse_as_infix("==", 10,
		 * InfixAssoc.RIGHT); parse_as_infix("===", 10, InfixAssoc.RIGHT);
		 * parse_as_infix("treal_eq", 10, InfixAssoc.RIGHT);
		 * parse_as_infix("IN", 11, InfixAssoc.RIGHT); parse_as_infix("belong",
		 * 11, InfixAssoc.RIGHT); parse_as_infix("--->", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("-->", 12, InfixAssoc.RIGHT); parse_as_infix("<", 12,
		 * InfixAssoc.RIGHT); parse_as_infix("<<", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("<<<", 12, InfixAssoc.RIGHT); parse_as_infix("<<=",
		 * 12, InfixAssoc.RIGHT); parse_as_infix("<=", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("=", 12, InfixAssoc.RIGHT); parse_as_infix(">", 12,
		 * InfixAssoc.RIGHT); parse_as_infix(">=", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("HAS_SIZE", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("PSUBSET", 12, InfixAssoc.RIGHT);
		 * parse_as_infix("SUBSET", 12, InfixAssoc.RIGHT);
		 * 
		 * parse_as_infix("+", 16, InfixAssoc.RIGHT); parse_as_infix("-", 18,
		 * InfixAssoc.LEFT); parse_as_infix("*", 20, InfixAssoc.RIGHT);
		 * parse_as_infix("/", 22, InfixAssoc.RIGHT);
		 */

		CamlList interfaceList = (CamlList) Parser.parse(infixes);
		for (int i = 0; i < interfaceList.size(); i++) {
			CamlPair p = (CamlPair) interfaceList.get(i);
			CamlString name = (CamlString) p.first();
			p = (CamlPair) p.second();
			CamlInt prec = (CamlInt) p.first();
			CamlString assoc = (CamlString) p.second();

			InfixAssoc a = assoc.equals("left") ? InfixAssoc.LEFT
					: InfixAssoc.RIGHT;
			parse_as_infix(name.str, prec.val, a);
		}

	}

	/**
	 * initPrefixes()
	 */
	public static void initPrefixes() throws Exception {
		// parse_as_prefix("~");
		// parse_as_prefix("--");
		// parse_as_prefix("mod");

		CamlList list = (CamlList) Parser.parse(prefixes);
		for (int i = 0; i < list.size(); i++) {
			CamlString name = (CamlString) list.get(i);
			parse_as_prefix(name.str);
		}
	}

	/**
	 * initBinders()
	 */
	public static void initBinders() throws Exception {
		/*
		 * parse_as_binder("\\"); parse_as_binder("!"); parse_as_binder("?");
		 * parse_as_binder("?!"); parse_as_binder("@");
		 * parse_as_binder("minimal"); parse_as_binder("lambda");
		 * parse_as_binder("lambdas");
		 */
		CamlList list = (CamlList) Parser.parse(binders);
		for (int i = 0; i < list.size(); i++) {
			CamlString name = (CamlString) list.get(i);
			parse_as_binder(name.str);
		}

	}

	/**
	 * initInterface()
	 */
	public static void initInterface() throws Exception {
		/*
		 * HOLType real = mk_type("real"); HOLType num = mk_type("num"); HOLType
		 * bool = mk_type("bool");
		 * 
		 * HOLType rrr = mk_fun_ty(real, mk_fun_ty(real, real)); HOLType rrb =
		 * mk_fun_ty(real, mk_fun_ty(real, bool)); HOLType rnr = mk_fun_ty(real,
		 * mk_fun_ty(num, real)); HOLType rr = mk_fun_ty(real, real); HOLType nr
		 * = mk_fun_ty(num, real);
		 * 
		 * overload_interface("+", mk_mconst("real_add", rrr));
		 * overload_interface("-", mk_mconst("real_sub", rrr));
		 * overload_interface("*", mk_mconst("real_mul", rrr));
		 * overload_interface("/", mk_mconst("real_div", rrr));
		 * overload_interface("<", mk_mconst("real_lt", rrb));
		 * overload_interface("<=", mk_mconst("real_le", rrb));
		 * overload_interface(">", mk_mconst("real_gt", rrb));
		 * overload_interface(">=", mk_mconst("real_ge", rrb));
		 * overload_interface("--", mk_mconst("real_neg", rr));
		 * overload_interface("pow", mk_mconst("real_pow", rnr));
		 * overload_interface("inv", mk_mconst("real_inv", rr));
		 * overload_interface("abs", mk_mconst("real_abs", rr));
		 * overload_interface("&", mk_mconst("real_of_num", nr));
		 */

		CamlList interfaceList = (CamlList) Parser.parse(the_interface);
		for (int i = 0; i < interfaceList.size(); i++) {
			CamlPair p = (CamlPair) interfaceList.get(i);
			CamlString name = (CamlString) p.first();
			p = (CamlPair) p.second();
			CamlString constName = (CamlString) p.first();
			HOLType type = (HOLType) p.second();

			overload_interface(name.str, mk_mconst(constName.str, type));
		}
	}

	public static void initSpecialPrinters() throws Exception {
		HOLType num = mk_type("num");
		// HOLType bool = mk_type("bool");
		HOLType nn = mk_fun_ty(num, num);

		// List
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op,
					ArrayList<Term> args, int prec) {
				Pair<ArrayList<Term>, Term> p = strip_right_binary("CONS", tm);
				Term nil = p.getSecond();

				if (!is_const(nil))
					return null;

				if (!dest_const(nil).getFirst().equals("NIL"))
					return null;

				TermPrinterTree node = new TermPrinterTree(tm, null);
				node.setBrackets("[", "]");
				return TermPrinter.print_term_sequence(node, "; ", 0, p.getFirst());
			}
		});

		// EMPTY
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op,
					ArrayList<Term> args, int prec) {
				if (s.equals("EMPTY") && is_const(tm) && args.size() == 0) {
					return new TermPrinterTree(tm, "{}");
				}

				return null;
			}
		});

		// INSERT
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op,	ArrayList<Term> args, int prec) {
				Pair<ArrayList<Term>, Term> p = strip_right_binary("INSERT", tm);
				Term nil = p.getSecond();

				if (!is_const(nil))
					return null;

				if (!dest_const(nil).getFirst().equals("EMPTY"))
					return null;
				
				TermPrinterTree node = new TermPrinterTree(tm, null);
				node.setBrackets("{", "}");

				return TermPrinter.print_term_sequence(node, ", ", 14, p.getFirst());
			}

		});

		// GSPEC
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op,	ArrayList<Term> args, int prec) {
				if (!s.equals("GSPEC"))
					return null;

				Term rand_tm = rand(tm);
				if (rand_tm == null)
					return null;

				Term b = body(rand_tm);
				if (b == null)
					return null;

				Pair<ArrayList<Term>, Term> pp = strip_binder("?", b);
				ArrayList<Term> evs = pp.getFirst();
				Term bod = pp.getSecond();

				Pair<Term, Term> p = dest_comb(bod);
				if (p == null)
					return null;

				Term bod1 = p.getFirst();
				Term fabs = p.getSecond();

				p = dest_comb(bod1);
				if (p == null)
					return null;

				Term bod2 = p.getFirst();
				Term babs = p.getSecond();

				Term c = rator(bod2);
				if (c == null)
					return null;

				if (!is_const(c))
					return null;

				if (!dest_const(c).getFirst().equals("SETSPEC"))
					return null;

				TermPrinterTree node = new TermPrinterTree(tm, null);
				node.setBrackets("{", "}");
				node.addBranch(TermPrinter.print_term(fabs, 0));
				node.addBranch(new TermPrinterTree(null, " | "));
				
				ArrayList<Term> fvs = fabs.frees();
				ArrayList<Term> bvs = babs.frees();
				
				ArrayList<Term> intersection;
				
				if (fvs.size() <= 1 || bvs.size() == 0)
					intersection = fvs;
				else {
					intersection = fvs;
					intersection.retainAll(bvs);
				}
				
				if (!evs.containsAll(intersection) || !intersection.containsAll(evs)) {
					TermPrinterTree seq = new TermPrinterTree(null, null);
					node.addBranch(TermPrinter.print_term_sequence(seq, ",", 14, evs));
					node.addBranch(new TermPrinterTree(null, " | "));
				}

				node.addBranch(TermPrinter.print_term(babs, 0));
				
				return node;
			}

		});
		
		
		// DECIMAL
		addSpecialPrinter(new SpecialPrinter() {
			private boolean powerof10(BigInteger n) {
				int flag = n.compareTo(BigInteger.ONE);
				
				if (flag < 0)
					return false;
				if (flag == 0)
					return true;
				
				return powerof10(n.divide(BigInteger.TEN));
			}
			
			@Override
			public TermPrinterTree print(Term tm, String s, Term op, ArrayList<Term> args, int prec) {
				if (!s.equals("DECIMAL") || args.size() != 2)
					return null;
				
				BigInteger n_num = dest_numeral(args.get(0));
				if (n_num == null)
					return null;
				
				BigInteger n_den = dest_numeral(args.get(1));
				if (n_den == null)
					return null;
				
				if (!powerof10(n_den))
					return null;
				
				String s_num = n_num.divide(n_den).toString();
				String s_den = n_num.mod(n_den).add(n_den).toString().substring(1);

				TermPrinterTree node = new TermPrinterTree(tm, "#");
				node.addBranch(new TermPrinterTree(args.get(0), s_num));
				
				if (!n_den.equals(BigInteger.ONE)) {
					node.addBranch(new TermPrinterTree(null, "."));
					node.addBranch(new TermPrinterTree(args.get(1), s_den));
				}
				
				return node;
			}
			
		});
		
		
		// COND
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op, ArrayList<Term> args, int prec) {
				if (!s.equals("COND") || args.size() != 3)
					return null;

				TermPrinterTree node = new TermPrinterTree(tm, "if ");
				
				if (prec != 0)
					node.setBrackets("(", ")");
				
				node.addBranch(TermPrinter.print_term(args.get(0), 0));
				node.addBranch(new TermPrinterTree(null, " then "));
				node.addBranch(TermPrinter.print_term(args.get(1), 0));
				node.addBranch(new TermPrinterTree(null, " else "));
				node.addBranch(TermPrinter.print_term(args.get(2), 0));
				
				return node;
			}
		});
		
		
		// NUMERAL
		final Term numeral = mk_mconst("NUMERAL", nn);

		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public TermPrinterTree print(Term tm, String s, Term op, ArrayList<Term> args, int prec) {
				if (op.equals(numeral) && args.size() > 0) {
					BigInteger r = dest_numeral(tm);
					if (r != null)
						return new TermPrinterTree(tm, r.toString());
				}

				return null;
			}

		});
	}
}
