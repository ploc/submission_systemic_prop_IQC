/* In this script, we verify the systemic properties of closed-loop system consisting of the augmented system H_tilde, which models the affine LPV controller, and the augmented system H, which models the nominal syste and is expressed as ghost code in this script.
*/

/* The plant has 4 states (x->x1,...,x->x4), 1 control input (u->u1), 1 disturbance input (d), and 1 output (y).
   The controller has 4 states (xc->x1,...,xc->x4).
*/

/* 
The interval bounds of the elements of the state vector are obtained by projecting the state invariant ellipsoid onto the plane of interest.
The state bounds are the following:
|x1| <= 2.2803;
|x2| <= 1.4714;
|x3| <= 2.2646;
|x4| <= 2.5125;
|xc1| <= 2.6205;
|xc2| <= 2.3859;
|xc3| <= 1.5325;
|xc4| <= 2.4305;

Bounds of theta obtained based on the remark in Section 3.3.2:
|theta0| <= 17.53;
|theta1| <= 12.32;
|theta2| <= 9.67;
|theta3| <= 36.67;
|theta4| <= 48.99;
|theta5| <= 34.36;

The output bound is the following:
|y| <= 2.2803;

The floating-point errors of each element of the augmented system H_tilde's state vector are computed using the tiny tool, and their values are the following:
State errors:
xc1:6.003966E-13
xc2:6.311802E-13
xc3:6.034432E-13
xc4:5.958014E-13
Max. Error e_x_H_tilde = 6.311802E-13

State errors of H:
x1:0
x2:0
x3:0
x4:0

State errors of the executable controller code:
xc1:1.954183E-13
xc2:2.202125E-13
xc3:2.021808E-13
xc4:1.953484E-13
Max. Error e_x_exe = 2.202125E-13

Hence, the maximum state floating-point error is e_xc = max(e_x_H_tilde,e_x_exe) = 6.311802E-13

The floating-point errors of the control input are computed using the tiny tool, and their values are the following:
e_u_H_tilde = 9.828567E-13
e_u_exe = 5.121239E-13

Hence, the maximum control input floating-point error is e_u = max(e_u_H_tilde,e_u_exe) = 9.828567E-13

Float Model Analysis:

State vector:
The radius of the error ball associated with the state vector is: r = (n_H+n_c) * e_xc = 8 * 6.311802E-13
The maximum and minimum eigenvalues of the matrix P (P is the matrix that defines the state-invariant ellipsoid) are computed using MATLAB's eig function.
MATLAB's algorithms for computing the eigenvalues of a positive definite matrix are generally accurate.
Nevertheless, to stay on the safe side, we manually choose a lower bound to the minimum eigenvalue of P and an upper bound to the maximum eigenvalue of P.
Namely, in this example, lambda_min(P) = 0.0657 and lambda_max(P) = 313.8052; hence, we choose the values 0.06 and 315 to be the lower and upper bound of lamda_min(P) and lambda_max(P), respectively.
Hence, norm_x_max = 1/sqrt(0.06) = 4.0825.

*/

//@   logic real e_xc = 6.311802E-13;
//@   logic real e_u = 9.828567E-13;


//@ predicate state_ellip(real x1, real x2, real x3, real x4, real x5, real x6, real x7, real x8, real lambda) = 144.771869 * x1 * x1 + 2 * -22.165479 * x1 * x2 + 2 * -17.175929 * x1 * x3 + 2 * 16.67008 * x1 * x4 + 2 * -121.38626 * x1 * x5 + 2 * 28.969347 * x1 * x6 + 2 * -65.40076999999999 * x1 * x7 + 2 * -25.21872 * x1 * x8 + 31.494369 * x2 * x2 + 2 * -8.612886 * x2 * x3 + 2 * -3.888473 * x2 * x4 + 2 * 30.563418 * x2 * x5 + 2 * -24.118686 * x2 * x6 + 2 * 35.120137 * x2 * x7 + 2 * -2.666092 * x2 * x8 + 12.213396 * x3 * x3 + 2 * -7.809983 * x3 * x4 + 2 * 6.638369 * x3 * x5 + 2 * 7.620935 * x3 * x6 + 2 * -11.803666 * x3 * x7 + 2 * 14.794701 * x3 * x8 + 14.026199 * x4 * x4 + 2 * -11.161903 * x4 * x5 + 2 * 0.396144 * x4 * x6 + 2 * 4.515306 * x4 * x7 + 2 * -17.872231 * x4 * x8 + 108.646952 * x5 * x5 + 2 * -34.488139 * x5 * x6 + 2 * 70.53336299999999 * x5 * x7 + 2 * 13.391488 * x5 * x8 + 21.745791 * x6 * x6 + 2 * -36.038315 * x6 * x7 + 2 * 5.184912 * x6 * x8 + 69.761832 * x7 * x7 + 2 * -12.406898 * x7 * x8 + 26.113558 * x8 * x8 <= lambda;

//@ predicate pwIQC_state(real r1, real r2, real r3, real r4, real r5, real r6, real r7, real r8, real r9, real r10, real r11, real r12) = 15.1249812 * r1 * r1 + 2 * 87.7605903 * r1 * r2 + 2 * -6.8084603 * r1 * r3 + 2 * 56.7228806 * r1 * r4 + 2 * -3.3522968 * r1 * r5 + 2 * 29.1140738 * r1 * r6 + 2 * 0 * r1 * r7 + 2 * -65.7265658 * r1 * r8 + 2 * 36.1489622 * r1 * r9 + 2 * -15.1379463 * r1 * r10 + 2 * -10.6545111 * r1 * r11 + 2 * -6.5967681 * r1 * r12 + 29860.4704226 * r2 * r2 + 2 * -11766.1239494 * r2 * r3 + 2 * 7640.272888 * r2 * r4 + 2 * 3043.6862567 * r2 * r5 + 2 * 3026.4731133 * r2 * r6 + 2 * 65.7265658 * r2 * r7 + 2 * 0 * r2 * r8 + 2 * 165.536934 * r2 * r9 + 2 * 139.9947875 * r2 * r10 + 2 * -68.8343237 * r2 * r11 + 2 * 78.02141810000001 * r2 * r12 + 4736.2356217 * r3 * r3 + 2 * -2992.9936111 * r3 * r4 + 2 * -1225.4310273 * r3 * r5 + 2 * -1177.5545494 * r3 * r6 + 2 * -36.1489622 * r3 * r7 + 2 * -165.536934 * r3 * r8 + 2 * 0 * r3 * r9 + 2 * -102.7320914 * r3 * r10 + 2 * 8.017224300000001 * r3 * r11 + 2 * -53.7436652 * r3 * r12 + 2245.5772607 * r4 * r4 + 2 * 708.0087545 * r4 * r5 + 2 * 916.1019379000001 * r4 * r6 + 2 * 15.1379463 * r4 * r7 + 2 * -139.9947875 * r4 * r8 + 2 * 102.7320914 * r4 * r9 + 2 * 0 * r4 * r10 + 2 * -32.0510033 * r4 * r11 + 2 * 7.1526306 * r4 * r12 + 333.1064001 * r5 * r5 + 2 * 273.4433902 * r5 * r6 + 2 * 10.6545111 * r5 * r7 + 2 * 68.8343237 * r5 * r8 + 2 * -8.017224300000001 * r5 * r9 + 2 * 32.0510033 * r5 * r10 + 2 * 0 * r5 * r11 + 2 * 15.7315518 * r5 * r12 + 377.2088387 * r6 * r6 + 2 * 6.5967681 * r6 * r7 + 2 * -78.02141810000001 * r6 * r8 + 2 * 53.7436652 * r6 * r9 + 2 * -7.1526306 * r6 * r10 + 2 * -15.7315518 * r6 * r11 + 2 * 0 * r6 * r12 + -15.1249812 * r7 * r7 + 2 * -87.7605903 * r7 * r8 + 2 * 6.8084603 * r7 * r9 + 2 * -56.7228806 * r7 * r10 + 2 * 3.3522968 * r7 * r11 + 2 * -29.1140738 * r7 * r12 + -29860.4704226 * r8 * r8 + 2 * 11766.1239494 * r8 * r9 + 2 * -7640.272888 * r8 * r10 + 2 * -3043.6862567 * r8 * r11 + 2 * -3026.4731133 * r8 * r12 + -4736.2356217 * r9 * r9 + 2 * 2992.9936111 * r9 * r10 + 2 * 1225.4310273 * r9 * r11 + 2 * 1177.5545494 * r9 * r12 + -2245.5772607 * r10 * r10 + 2 * -708.0087545 * r10 * r11 + 2 * -916.1019379000001 * r10 * r12 + -333.1064001 * r11 * r11 + 2 * -273.4433902 * r11 * r12 + -377.2088387 * r12 * r12 >= 0;

// The IQC filter is static; hence we compute the plant states using x(k+1) = Ass*x(k) + Asp*theta(k) + B1s*d(k) + B2s*u(k)

// Logic Functions to Compute the Nominal System States (x1,x2,x3,x4):
/*@
  logic real update_x1 (real pre_x1, real pre_x2, real pre_x3, real pre_x4, real d, real theta0, real u) = 1 * pre_x1 + 0.1 * pre_x2 + 0 * pre_x3 + 0 * pre_x4 + 0 * theta0 + 0 * u;
  logic real update_x2 (real pre_x1, real pre_x2, real pre_x3, real pre_x4, real d, real theta0, real u) = -0.075 * pre_x1 + 0.996 * pre_x2 + 0.075 * pre_x3 + 0.004 * pre_x4 + 0.18756 * theta0 + 0 * u;
  logic real update_x3 (real pre_x1, real pre_x2, real pre_x3, real pre_x4, real d, real theta0, real u) = 0 * pre_x1 + 0 * pre_x2 + 1 * pre_x3 + 0.1 * pre_x4 + 0 * theta0 + 0 * u;
  logic real update_x4 (real pre_x1, real pre_x2, real pre_x3, real pre_x4, real d, real theta0, real u) = 0.0075 * pre_x1 + 0.0004 * pre_x2 + -0.0075 * pre_x3 + 0.9996 * pre_x4 + -0.01876 * theta0 + 0.1 * d + 0.1 * u;
 */


typedef struct { double x1, x2, x3, x4; } state;

typedef struct {double u1;} control_input;

/*@
    requires \valid(xc) && \valid(u);
    requires -0.1 <= d <= 0.1;
    requires \separated(&(xc->x1),&(xc->x2),&(xc->x3),&(xc->x4),&(u->u1));
    requires state_ellip(x1, x2, x3, x4, xc->x1, xc->x2, xc->x3, xc->x4, 1);
    
    requires pwIQC_state(-0.13329 * x1 + 0 * x2 + 0.13329 * x3 + 0 * x4 + 0 * xc->x1 + 0 * xc->x2 + 0 * xc->x3 + 0 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, 0 * x1 + 0 * x2 + 0 * x3 + 0 * x4 + -0.15503 * xc->x1 + 0.03198 * xc->x2 + -0.09787999999999999 * xc->x3 + -0.00532 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, 0 * x1 + 0 * x2 + 0 * x3 + 0 * x4 + 0.65434 * xc->x1 + -0.14282 * xc->x2 + 0.30492 * xc->x3 + 0.03626 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, 1.0053 * x1 + 0 * x2 + 0 * x3 + 0 * x4 + 0.6169 * xc->x1 + -0.12217 * xc->x2 + 0.34429 * xc->x3 + 0.03196 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, 0 * x1 + 0 * x2 + 0 * x3 + 0 * x4 + 2.29189 * xc->x1 + -0.51695 * xc->x2 + 1.15661 * xc->x3 + 0.10179 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, -2.57059 * x1 + 0 * x2 + 0 * x3 + 0 * x4 + 0.24126 * xc->x1 + -0.04778 * xc->x2 + 0.13465 * xc->x3 + 0.0125 * xc->x4 + 0 * theta0 + 0 * theta1 + 0 * theta2 + 0 * theta3 + 0 * theta4 + 0 * theta5 + 0 * d, theta0, theta1, theta2, theta3, theta4, theta5);
    
    requires y == x1;
    assigns *xc, *u;
    
    // Real model:
    ensures \let nx1 = update_x1 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1);
    	    \let nx2 = update_x2 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1); 
    	    \let nx3 = update_x3 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1); 
    	    \let nx4 = update_x4 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1);  
    	    state_ellip(nx1, nx2, nx3, nx4, xc->x1, xc->x2, xc->x3, xc->x4, 1);
    
    // Float model:
    ensures \forall real l;
            \let nx1 = update_x1 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1 + l * e_u);
            \let nx2 = update_x2 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1 + l * e_u);
            \let nx3 = update_x3 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1 + l * e_u); 
            \let nx4 = update_x4 (\at(x1, Pre), \at(x2, Pre), \at(x3, Pre), \at(x4, Pre), d, theta0, u->u1 + l * e_u);  
            -1 <= l <= 1 ==> state_ellip(nx1, nx2, nx3, nx4, xc->x1, xc->x2, xc->x3, xc->x4, 1 - 2 * 8 * e_xc * 315 * 4.0825 - 8 * e_xc * 8 * e_xc * 315);


*/
void controller_model(state *xc, control_input *u, double y, double theta1, double theta2, double theta3, double theta4, double theta5) /*@ ghost (double x1, double x2, double x3, double x4, double theta0, double d) */ {
    double pre_xc1 = xc->x1, pre_xc2 = xc->x2, pre_xc3 = xc->x3, pre_xc4 = xc->x4;

    // Compute control inputs
    u->u1 = 21.28825 * pre_xc1 + -5.09412 * pre_xc2 + 11.70845 * pre_xc3 + -1.79242 * pre_xc4 + -0.23417 * theta1 + 0.29857 * theta2 + -0.94052 * theta3 + 2.58161 * theta4 + 2.20277 * theta5 + -23.56524 * y;
    
    // Update controller states
    xc->x1 = 1.17757 * pre_xc1 + 0.15468 * pre_xc2 + 0.3614 * pre_xc3 + 0.07437000000000001 * pre_xc4 + 0.61714 * theta1 + -0.78684 * theta2 + 0.20519 * theta3 + 0.15518 * theta4 + 0.03225 * theta5 + -0.34712 * y;
    xc->x2 = -3.70972 * pre_xc1 + 1.5429 * pre_xc2 + -2.65686 * pre_xc3 + -0.19578 * pre_xc4 + 0.11973 * theta1 + -0.15266 * theta2 + -0.82326 * theta3 + 0.03011 * theta4 + -0.62547 * theta5 + 4.32037 * y;
    xc->x3 = -2.28481 * pre_xc1 + 0.18366 * pre_xc2 + -1.01544 * pre_xc3 + -0.17827 * pre_xc4 + 0.66816 * theta1 + 0.46416 * theta2 + -0.09265 * theta3 + -0.09154 * theta4 + -0.07739 * theta5 + 2.82567 * y;
    xc->x4 = 0.82117 * pre_xc1 + -0.37183 * pre_xc2 + 0.04747 * pre_xc3 + 0.73553 * pre_xc4 + 0.46416 * theta1 + 0.44041 * theta2 + 0.05392 * theta3 + 0.11672 * theta4 + 0.26285 * theta5 + -0.74581 * y;
}
