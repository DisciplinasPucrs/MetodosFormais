ghost predicate sorted(a: array<int>)
  reads a
{
    forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

//exemplo gerado pelo ChatGPT
method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires sorted(a)
  ensures exists i :: ((0 <= i < a.Length && a[i] == value) ==> index == i)
  ensures forall i :: ((0 <= i < a.Length ==> a[i] != value) ==> index == -1)
{
    var low := 0;
    var high := a.Length - 1;
    while low <= high
      invariant forall i :: 0 <= i < low ==> a[i] < value
      invariant forall i :: high < i < a.Length ==> a[i] > value
    {
        var mid := (low + high) / 2;
        if a[mid] == value
        {
            return mid;
        }
        else if a[mid] < value
        {
            low := mid + 1;
        }
        else
        {
            high := mid - 1;
        }
    }
    return -1;
}