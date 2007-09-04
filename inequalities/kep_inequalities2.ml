(* ----------------------------------------------------------------------- *)
(* 
latex-format comment

\section{Notes on Interval Verifications}
    %{Appendix 2. Interval Verifications}
    \label{sec:verification-notes}

We make a few remarks in this appendix on the verification of the
inequalities of Proposition~\ref{calc:quad-bounds} and \ref{calc:d(R)}.
The basic method in proving an inequality $f(x)<0$ for $x\in C$, is to
use computer-based interval arithmetic to obtain rigorous upper bounds
on the second derivatives: $|f_{ij}(x)|\le a_{ij}$, for $x\in C$.  These
bounds lead immediately to upper bounds on $f(x)$ through a Taylor
approximation with explicit bounds on the error.  We divide the domain
$C$ as necessary until the Taylor approximation on each piece is less
that the desired bound.

Some of the inequalities involve as many as $12$ variables, such as the
octahedral cases of Lemma~\ref{calc:d(R)}.  These are not directly
accessible by computer.  We describe some reductions we have used, based
on linear programming. We start by applying the dimension reduction
techniques described in~\cite[Sec.~8.7]{part1}.  We have used these
whenever possible.

We will describe Lemma~\ref{calc:d(R)} because in various respects these
inequalities have been the most difficult to prove, although the
verifications of Lemmas~\ref{calc:quad-bounds} and \ref{lemma:1.153} are
quite similar. If there is a diagonal of length $\le2\sqrt{2}$, we have
two flat quarters $S_1$ and $S_2$.  The score breaks up into
    $\sigma=\sigma(S_1)+\sigma(S_2)$.  The simplices $S_1$ and
$S_2$ share a three-dimensional face.   The inequality we wish to prove
has the form
    $$\sigma \le a(\dih(S_1)+\dih_2(S_1)+\dih_2(S_2))+b.$$
We break the shared face into smaller domains on which we have
    $$
    \begin{array}{lll}
    \sigma(S_1)&\le a (\dih(S_1)+\dih_2(S_1)) + b_1,\\
    \sigma(S_2)&\le a \dih_2(S_1) + b_2,\\
    \end{array}
    $$
for some $b_1,b_2$ satisfying $b_1+b_2\le b$.  These inequalities are
six-dimensional verifications.

If the quad cluster is an octahedron with upright diagonal, there are
four upright quarters $S_1,\ldots,S_4$. We consider inequalities of the
form
    \begin{equation}
    \sigma(S_i)\le \sum _{j\ne 4} a_j^i y_j(S_i)
    + a_7 (\dih_1(S_i)-\pi/2) + \sum_{j=2}^3 a \epsilon^i_j \dih_j(S_i)
    + b^i.
    \label{eqn:Xi}
    \end{equation}
If $\sum_{i=1}^4 a_j^i \le0$, $j\ne 4$, and $\sum_i b^i\le b$, then for
appropriate $\epsilon^i_j\in\{0,1\}$, these inequalities imply the full
inequality for octahedral quad clusters.

By linear programming techniques, we were able to divide the domain of
all octahedra into about $1200$ pieces and find inequalities of this
form on each piece, giving an explicit list of inequalities that imply
Lemma~\ref{calc:d(R)}.  The inequalities involve six variables and were
verified by interval arithmetic.

To find the optimal coefficients $a_j^i$ by linear programming we pose
the linear problem
    $$
    \begin{array}{lll}
    &\max t \\
    &\hbox{such that}\\
    &\quad X_i,\quad i=1,2,3,4, \ \{S_1,S_2,S_3,S_4\}\in C\\
    &\quad\sum_i a_j^i \le 0,\\
    &\quad\sum_i b^i \le b,
    \end{array}
    $$
where $\{S_1,S_2,S_3,S_4\}$ runs over all octahedra in a given domain
$C$. The nonlinear inequalities~\ref{eqn:Xi} are to be regarded as
linear conditions on the coefficients $a_j^i$, $b^i$, etc. The nonlinear
functions $\sigma(S_i),\dih(S_i)$, $y_j(S_i)$ are to be regarded as the
coefficients of the variables $a_j^i,\ldots$ in a system of linear
inequalities.  There are infinitely many constraints, because the set
$C$ of octahedra is infinite.  In practice we approximate $C$ by a large
finite set.  If the maximum of $t$ is positive, then we have a
collection of inequalities in small dimensions that imply the inequality
for octahedral quad clusters.  Otherwise, we subdivide $C$ into smaller
domains and try again.  Eventually, we succeed in partitioning the
problem into six-dimensional pieces, which were verified by interval
methods.

\smallskip
If the quad cluster is a mixed case, then Lemma~\ref{lemma:1.04} gives
    $$\sigma\le \vor_0, -1.04\,\pt,$$ so also
    $$\sigma \le \frac{3}{4}\vor_0 + \frac{1}{4} (-1.04\,\pt).$$
In the pure Voronoi case with no quarters and no enclosed vertices, we
have the approximation
    $$\sigma \le \vor(\cdot,\sqrt2) \le \vor_0.$$
If we prove $\vor_0\le a (\dih_1+\dih_2) + b$, the mixed case is
established. This is how the first of the Inequalities~\ref{calc:d(R)}
was established. Dimension reduction reduces this to a seven-dimensional
verification. We draw the shorter of the two diagonals between corners
of the quad cluster. As we begin to subdivide this seven-dimensional
domain, we are able to separate the quad cluster into two simplices
along the diagonal, each scored by $\vor_0$.  This reduces the dimension
further, to make it accessible.  The two last two cases of
Inequality~\ref{calc:d(R)}, are similar, but we establish the
inequalities
    $$
    \begin{array}{lll}
    \frac{3}{4}\vor_0 + \frac{1}{4} (-1.04\,\pt) &\le a (\dih_1+\dih_2) + b,\\
    \vor(\cdot,\sqrt2)&\le a (\dih_1+\dih_2) + b.
    \end{array}
    $$
This completes our sketch of how the verifications were made.


*)


(* now we can list inequalities *)

(* SPIII-1998 Lemma 4.1 *)


let J_310151857 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < --(&57906)/(&10000)
                + ((&456766)/(&100000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_655029773 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < --(&20749)/(&10000)
                + ((&15094)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_73283761 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < --(&8341)/(&10000)
                + ((&5301)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_15141595 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < --(&6284)/(&10000)
                + ((&3878)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_574391221 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < (&4124)/(&10000)
                - ((&1897)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_396281725 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < (&15707)/(&10000)
                - ((&5905)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_166451608 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4) < (&41717)/(&100000)
                - ((&3)/(&10))*(solid_area_quad_v v0 v1 v2 v3 v4)))`);;
let J_539320075 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < --(&581446)/(&100000)
                + ((&449461)/(&100000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_122375455 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < --(&2955)/(&1000)
                + ((&21406)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_408478278 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < --(&6438)/(&10000)
                + ((&316)/(&1000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_996268658 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < --(&1317)/(&10000)))`);;
let J_393682353 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < (&3825)/(&10000)
                - ((&2365)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_775642319 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 (&1)) < (&1071)/(&1000)
                - ((&4747)/(&10000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_616145964 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 ((&32)/(&10))) <
        --(&577942)/(&100000)
                + ((&425863)/(&100000))*(dih_or_v v0 v1 v2 v4)))`);;
let J_153920401 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 ((&32)/(&10)) <
        --(&4893)/(&1000)
                + ((&35294)/(&10000))*(dih_or_v v0 v1 v2 v4))))`);;
let J_337637212 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 ((&32)/(&10)) <
        --(&4126)/(&10000))))`);;
let J_768057794 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1_lambda v0 v1 v2 v3 v4 ((&32)/(&10)) <
        (&33)/(&100)
                - ((&316)/(&1000))*(dih_or_v v0 v1 v2 v4))))`);;
let J_465497818 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- ((&419351)/(&1000000))*(solid_area_quad_v v0 v1 v2 v3 v4)
        - (&5350181)/(&1000000)
                + ((&4611391)/(&1000000))*(dih_or_v v0 v1 v2 v4))))`);;
let J_18502666 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- ((&419351)/(&1000000))*(solid_area_quad_v v0 v1 v2 v3 v4)
        - (&166174)/(&100000)
                + ((&1582508)/(&1000000))*(dih_or_v v0 v1 v2 v4))))`);;
let J_676439533 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- ((&419351)/(&1000000))*(solid_area_quad_v v0 v1 v2 v3 v4)
        + (&895)/(&10000)
                + ((&342747)/(&1000000))*(dih_or_v v0 v1 v2 v4))))`);;
let J_974296985 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- ((&419351)/(&1000000))*(solid_area_quad_v v0 v1 v2 v3 v4)
        + (&336909)/(&100000)
                - ((&974137)/(&1000000))*(dih_or_v v0 v1 v2 v4))))`);;

let C_940884472 = list_mk_conj[ 
  J_310151857;
  J_655029773;
  J_73283761;
  J_15141595;
  J_574391221;
  J_396281725;
  J_166451608;
  J_539320075;
  J_122375455;
  J_408478278;
  J_996268658;
  J_393682353;
  J_775642319;
  J_616145964;
  J_153920401;
  J_337637212;
  J_768057794;
  J_465497818;
  J_18502666 ;
  J_676439533;
  J_974296985;];;


(* SPIII-1998 Lemma 4.2 *)

let J_322621318 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- (&9494)/(&1000)
                + ((&30508)/(&100000))*
                ((dih_or_v v0 v1 v2 v4)+
                (dih_or_v v0 v2 v3 v1)))))`);;
let J_444643063 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
        -- (&10472)/(&100000)
                + ((&27605)/(&100000))*
                ((dih_or_v v0 v1 v2 v4)+
                (dih_or_v v0 v2 v3 v1)))))`);;
let J_552698390 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((sigma_quad_approx1 v0 v1 v2 v3 v4 <
         (&35926)/(&10000)
                - ((&844)/(&1000))*
                ((dih_or_v v0 v1 v2 v4)+
                (dih_or_v v0 v2 v3 v1)))))`);;

(* SPIII-1998 Lemma 4.3 *)

let J_657406669 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((#1.153) < dih_or_v v0 v1 v2 v4))`);;
let J_277330628 = (`!v0 v1 v2 v3 v4. ((is_quad_cluster_v v0 v1 v2 v3 v4) ==>
        ((dih_or_v v0 v1 v2 v4) < (#3.247)))`);;



