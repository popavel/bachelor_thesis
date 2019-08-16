procedure multiply_by_4(m: int) returns(res: int)
    requires m > 0;
    ensures res == 4 * m;
{
    var i: int;
    var j: int;
	var d: real;
	d := 0.5;
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
	i := 1 + j;
	j := 2;
	
	if ( i < j) 
	{
		j := i;
	} else if (i > 0) 
	{
		j := j * 2;
	} else	
	{
		i := j;
	}
	
	j := i + 1;
}
