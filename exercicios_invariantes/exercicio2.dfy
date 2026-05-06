method FazAlgo(c:int)
{
    var x := c;
    var y := 0;
    while x > 0
      invariant c == x+y
    {
        x := x-1;
        y := y+1;
    }
}
