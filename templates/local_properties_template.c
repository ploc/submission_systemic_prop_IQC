typedef struct { double x1,... , x_nH; } state;

typedef struct { double y1,... , y_ny; } output;

//@ predicate state_ellip(real x1,... , real x_nH, real lambda) = P_11 * x1 * x1 + 2 * P_12 * x1 * x2 + ... + P_nHnH * x_nH * x_nH <= lambda;

//@ predicate output_ellip(real y1,... , real y_ny, real lambda) = Q_11 * y1 * y1 + 2 * Q_12 * y1 * y2 + ... + Q_nyny * y_ny * y_ny <= lambda;

//@ predicate pwIQC_state(real r1,... , real r_nr) = Sx_11 * r1 * r1 + ... + Sx_nrnr * r_nr * r_nr >= 0;

//@ predicate pwIQC_output(real r1,... , real r_nr) = Sy_11 * r1 * r1 + ... + Sy_nrnr * r_nr * r_nr >= 0;

/*@
requires \valid(x);

requires \separated(&(x->x1),... ,&(x->x_nH));

// Replace r1, r2,..., r_nr with their expressions in terms of x, theta, and d based on the state-space equations of the augmented system H.
requires pwIQC_state(r1,... , r_nr);

assigns *x;

behavior polytope_input_real_model:
	 assumes -d1_bar <= d1 <= d1_bar;
	 .
	 .
	 .
	 assumes -d_nd_bar <= d_nd <= d_nd_bar;

	 ensures state_ellip(\old(x->x1),... , \old(x->x_nH), 1) ==> state_ellip(x->x1,... , x->x_nH, 1);

behavior polytope_input_float_model:
	 assumes -d1_bar <= d1 <= d1_bar;
	 .
	 .
	 .
	 assumes -d_nd_bar <= d_nd <= d_nd_bar;

// Replace alpha_x with its expression in Section 3.2
	 ensures state_ellip(\old(x->x1),... , \old(x->x_nH), 1) ==> state_ellip(x->x1,... , x->x_nH, alpha_x);
*/

void updateState(state *x, double theta1,... , double theta_ntheta, double d1,... , double d_nd) {
	 double pre_x1 = x->x1,... , pre_x_nH = x->x_nH;

// Update the state vector based on the state-space equations of the augmented system H.
	 x->x1 = ...;
	 .
	 .
	 .
	 x->x_nH = ...;
}

/*@
requires \valid(x);
requires \valid(y);

requires \separated(&(x->x1),... ,&(x->x_nH),&(y->y1),... ,&(y->y_ny));

// Replace r1, r2,..., r_nr with their expressions in terms of x, theta, and d based on the state-space equations of the augmented system H.
requires pwIQC_output(r1,... , r_nr);

assigns *y;

behavior polytope_input_real_model:
	 assumes -d1_bar <= d1 <= d1_bar;
	 .
	 .
	 .
	 assumes -d_nd_bar <= d_nd <= d_nd_bar;

	 ensures state_ellip(\old(x->x1),... , \old(x->x_nH), 1) ==> output_ellip(y->y1,... , y->y_ny, 1);

behavior polytope_input_float_model:
	 assumes -d1_bar <= d1 <= d1_bar;
	 .
	 .
	 .
	 assumes -d_nd_bar <= d_nd <= d_nd_bar;

// Replace alpha_y with its expression in Section 3.2
	 ensures state_ellip(\old(x->x1),... , \old(x->x_nH), 1) ==> output_ellip(y->y1,... , y->y_ny, alpha_y);
*/

void updateOutput(state *x, output *y, double theta1,... , double theta_ntheta, double d1,... , double d_nd) {
	 double pre_x1 = x->x1,... , pre_x_nH = x->x_nH;

// Compute the output vector based on the state-space equations of the augmented system H.
	 y->y1 = ...;
	 .
	 .
	 .
	 y->y_ny = ...;
}
