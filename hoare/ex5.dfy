method Exemplo(x:int) returns (i:int)
  ensures i <= 0
{
  i := x;
  while i > 0
    //invariant true
    //decreases i
  {
    i := i-1;
  }
  assert i <= 0;
}