class WrapArray
{
  var intarray: array<int>
  constructor (i:int) 
    requires i > 0
    ensures fresh(intarray)
  {
    intarray := new int[i];
  }
  method init(i: int)
    modifies intarray
  {
    var index: int := 0;
    while (index < intarray.Length)
    {
      intarray[index] := i;
      index := index+1;
    }
  }
}

method Main()
{
  var sh:= new WrapArray(5);
  sh.init(4);
}
