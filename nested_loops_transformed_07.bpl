// ORIGINAL METHOD /////////////////////////////
procedure multiply_by_4(m: int) returns(res: int)
    requires m > 0;
    ensures res == 4 * m;
{
    var i: int;
    var j: int;
    i := 0;
    j := 0;
    res := 0;
    
    while (i < 4)
        invariant res == m * i; 
        invariant i <= 4;
        invariant j == 0;
    {
        while (j < m)
            invariant res == (m * i) + j;
            invariant j <= m;
        {
            j := j + 1;
            res := res + 1;
        }
        i := i + 1;
        j := 0;
    }
} 

// TRANSFORMED METHOD //////////////////////////////////////
// invariants for the outer loop:
//      res == m * i
//      i <= 4
//      j == 0
// invariants for the inner loop:
//      res == m * i + j
//      j <= m
procedure multiply_by_4_transformed(m: int) returns(res: int)
    requires m > 0;
    ensures res == 4 * m;
{
		// invariant flags of the outer loop
    var inv1: bool;
    var inv2: bool;
    var inv3: bool;
    var inv1_b: bool;
    var inv2_b: bool;
    var inv3_b: bool;
    var inv1_a: bool;
    var inv2_a: bool;
    var inv3_a: bool;

    // invariant flags for the inner loop
    var inv4_1: bool;
    var inv5_1: bool;
    var inv4_b_1: bool;
    var inv5_b_1: bool;
    var inv4_a_1: bool;
    var inv5_a_1: bool;

		// flag for the inner loop condition
		var lc1: bool;

		// variables for actual loop simulation
		var star: bool; // outer loop
		var star1: bool; // inner loop
		
    // duplicate all target variables
    var i1: int;
    var j1: int;
    var res1:int;

    var i: int;
    var j: int;
    i := 0;
    j := 0;
    res := 0;
   
    // check whether an invariant holds before the outer loop
    assume res == m * i <==> inv1_b;
    assume i <= 4 <==> inv2_b;
    assume j == 0 <==> inv3_b;

    // simulate an arbitrary iteration
    call i1 := havocInt();
    call j1 := havocInt();
    call res1 := havocInt();
    assume inv1_a ==> res1 == m * i1;
    assume inv2_a ==> i1 <= 4;
    assume inv3_a ==> j1 == 0;

    //////////////////////////////////////////
    // infer invariants for the outer loop ///
    //////////////////////////////////////////

    // we only simulate the outer loop, if we can ever enter it
    // we do not need the duplicates in the if clause for the outer loop
		if (i < 4) {
        assume i1 < 4; // loop condition
    
        // transformed loop body

        // check whether an invariant holds before the inner loop
        assume res1 == m * i1 + j1 <==> inv4_b_1;
        assume j1 <= m <==> inv5_b_1;

        // check the inner loop condition
        assume j1 < m <==> lc1; 
        
        // simulate an arbitrary iteration of an inner loop
        call j1 := havocInt();
        call res1 := havocInt();
        assume inv4_a_1 ==> res1 == (m * i1) + j1;
        assume inv5_a_1 ==> j1 <= m;
        
        // we only simulate the inner loop, if we can ever enter it
        if (lc1) {
            // inner loop condition
            assume j1 < m;

            // transformed inner loop body
            j1 := j1 + 1;
            res1 := res1 + 1;
        }
        // infer, which invariants hold
        // one invariant
        assume ( inv4_b_1 && ( inv4_a_1 ==> (res1 == m * i1 + j1) ) ) ==> inv4_1;
        assume ( inv5_b_1 && ( inv5_a_1 ==> (j1 <= m) ) ) ==> inv5_1;
        // two invariants
        // maybe this is not needed if there is no further nested loop
        assume ( inv4_b_1 && inv5_b_1 && ( (inv4_a_1 && inv5_a_1) ==> ( (res1 == m * i1 + j1) && (j1 <= m) ) ) )
				==> (inv4_1 && inv5_1);
        
        // negate inner loop condition    
        assume !(j1 < m);
        assume inv4_1 ==> res1 == m * i1 + j1;
        assume inv5_1 ==> j1 <= m;

        // back to outer loop
        i1 := i1 + 1;
        j1 := 0;
    }
    // infer, which invariants hold
    // one invariant
    assume (inv1_b && (inv1_a ==> res1 == m * i1)) ==> inv1;
    assume (inv2_b && (inv2_a ==> i1 <= 4)) ==> inv2;
    assume (inv3_b && (inv3_a ==> j1 == 0)) ==> inv3;
    // two invariants
    assume ( inv1_b && inv2_b && ( (inv1_a && inv2_a) ==> ((res1 == m * i1) && (i1 <= 4)) ) ) ==> (inv1 && inv2);
    assume ( inv1_b && inv3_b && ( (inv1_a && inv3_a) ==> ((res1 == m * i1) && (j1 == 0)) ) ) ==> (inv1 && inv3);
    assume ( inv2_b && inv3_b && ( (inv2_a && inv3_a) ==> ((i1 <= 4) && (j1 == 0)) ) ) ==> (inv2 && inv3);
    // three invariants
    assume ( inv1_b && inv2_b && inv3_b && ( (inv1_a && inv2_a && inv3_a) ==> ((res1 == m * i1) && (i1 <= 4)) && (j1 == 0)) )
		==> (inv1 && inv2 && inv3);
   
    assert inv1;
    assert inv2;
    assert inv3;
    // here invariants for the outer loop are known ///
    ///////////////////////////////////////////////////

    // this is to be able to infer invariants for the inner loop
    assume inv1 ==> inv1_a;
    assume inv2 ==> inv2_a;
    assume inv3 ==> inv3_a;

    assert inv5_1;
    assert inv4_1;
    // here invariants for the inner loop are known ///
    ///////////////////////////////////////////////////

    // actual loop
    call i := havocInt();
    call j := havocInt();
    call res := havocInt();
    assume inv1 ==> res == m * i;
    assume inv2 ==> i <= 4;
    assume inv3 ==> j == 0;

    if (star) {
        assume i < 4;

        // actual inner loop
        call j := havocInt();
        call res := havocInt();
        assume inv4_1 ==> res == m * i + j;
        assume inv5_1 ==> j <= m;

        if (star1) {
            assume j < m;

            j := j + 1;
            res := res + 1;

            assume false;
        } else {
            assume !(j < m);
        }

        // back to outer loop
        i := i + 1;
        j := 0;

        assume false;
    } else {
        assume !(i < 4);
    }
    
}

procedure havocInt() returns(res: int) {}
