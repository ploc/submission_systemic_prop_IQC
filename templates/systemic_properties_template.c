/* First, we define
   - the state_ellip predicate describing the state invariant ellipsoid
   - one logic function for each plant state that corresponds to the computation of that state.  
    (The logic functions are not mandatory but will facilitate writing contracts.)
*/

//@ predicate state_ellip(real x1,..., real x_ncl, real lambda) = ...;

//@ predicate pwIQC_state(real r1,... , real r_nr) = Sx_11 * r1 * r1 + ... + Sx_nrnr * r_nr * r_nr >= 0;

// Logic Functions to compute the augmented states based on x(k+1) = A_H*x(k) + B_H1*theta(k) + B_H2*d(k) + B_H3*u(k)
// Computing x1
/*@
  logic real update_x1 (real pre_x1, ..., real pre_x_nH, real d1, ..., real d_nd, real theta1, ..., real theta_ntheta, real u1, ..., real u_nu) = 
  (Equation)
 */

// Computing x_nH
/*@
  logic real update_x_nH (real pre_x1, ..., real pre_x_nH, real d1, ..., real d_nd, real theta1, ..., real theta_ntheta, real u1, ..., real u_nu) = 
  (Equation)
 */

typedef struct { double x1, ..., x_nc; } state;

typedef struct {double u1, ..., u_nu;} control_input;

/*@
    requires \valid(xc) && \valid(u);
    requires -d1_bar <= d1 <= d1_bar;
    .
    .
    .
    requires -d_nd_bar <= d_nd <= d_nd_bar;
    requires \separated(&(xc->x1),...,&(xc->x_nc),&(u->u1),...,&(u->u_nu));
    requires state_ellip(x1, ..., x_nH, xc->x1, ..., xc->x_nc, 1);
    
    // Replace r1, r2,..., r_nr with their expressions in terms of x_cl, theta, d, and u based on the state-space equations of the augmented system H.
    requires pwIQC_state(r1,... , r_nr);
    
    // Require that the output vector satisfies the output equations
    requires y1 == ...;
    .
    .
    .
    requires y_ny == ...;
    assigns *xc, *u;
    
    // Real model:
    ensures \let nx1 = update_x1 (\at(x1, Pre), ..., \at(x_nH, Pre), d1, ..., d_nd, theta1, ..., theta_ntheta, u->u1, ..., u->u_nu);
    	.
    	.
    	.
        \let nx_nH = update_x_nH (\at(x1, Pre), ..., \at(x_nH, Pre), d1, ..., d_nd, theta1, ..., theta_ntheta, u->u1, ..., u->u_nu);
        state_ellip(nx1, ..., nx_nH, xc->x1, ..., xc->x_nc, 1);

	// Float model (replace alpha with its expression in Section 4.2):
    ensures \forall real l_1; ...; \forall real l_nu;
        \let nx1 = update_x1 (\at(x1, Pre), ..., \at(x_nH, Pre), d1, ..., d_nd, theta1, ..., theta_ntheta, u->u1 + l_1 * e_u, ..., u->u_nu + l_nu * e_u);
    	.
    	.
    	.
        \let nx_nH = update_x_nH (\at(x1, Pre), ..., \at(x_nH, Pre), d1, ..., d_nd, theta1, ..., theta_ntheta, u->u1 + l_1 * e_u, ..., u->u_nu + l_nu * e_u);
        -1 <= l_1 <= 1 ==> ... ==> -1 <= l_nu <= 1 ==>
        state_ellip(nx1, ..., nx_nH, xc->x1, ..., xc->x_nc, alpha);
*/
void controller(state *xc, control_input *u, double y1, ..., double y_ny) /*@ ghost (double x1, ..., double x_nH, double theta1, ..., double theta_ntheta, double d1, ..., double d_nd) */ {
    double pre_xc1 = xc->x1, ..., pre_xc_nc = xc->x_nc;

    // Compute control inputs
    u->u1 = ...;
    .
    .
    .
    u->u_nu = ...;
    
    // Update controller states
    xc->x1 = ...;
    .
    .
    .
    xc->x_nc = ...;
}
