class WrapArray
{
  var intarray: array<int>
  constructor (i:int) 
    requires i > 0
    ensures intarray.Length == i
    ensures fresh(intarray)
  {
    intarray := new int[i];
  }
  method init(i: int)
    modifies intarray
    ensures forall j :: 0 <= j < intarray.Length ==> intarray[j] == i
  {
    var index: int := 0;
    while (index < intarray.Length)
      invariant 0 <= index <=  intarray.Length
      invariant forall j :: 0 <= j < index ==> intarray[j] == i
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
