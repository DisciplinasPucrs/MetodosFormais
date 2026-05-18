ghost predicate sorted(a: array<int>)
  reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
    var low, high := 0, a.Length;
    while low < high
      invariant 0 <= low <= high <= a.Length
      invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
    {
      var mid := (low + high) / 2;
      if a[mid] < value
      {
        low := mid + 1;
      }
      else if value < a[mid]
      {
        high := mid;
      }
      else
      {
        return mid;
      }
    }
    return -1;
}

method Main()
{
  var numeros := new int[5];
  numeros[0] := 1;
  numeros[1] := 3;
  numeros[2] := 4;
  numeros[3] := 6;
  numeros[4] := 7;
  var resultado := BinarySearch(numeros,1);
  assert numeros[0] == 1;
  assert resultado >= 0;
  assert numeros[resultado] == 1;
}
