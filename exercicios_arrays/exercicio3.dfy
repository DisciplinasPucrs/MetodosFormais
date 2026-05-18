method FindMaxIndex(a:array<int>) returns (i:int)
  requires a.Length > 0
  ensures 0 <= i < a.Length //é um índice válido
  ensures forall j :: 0 <= j < a.Length ==> a[j] <= a[i] //é o índice do maior elemento
  //a seguinte pós-condição é desencessária, pois não existe cláusula modifies no método
  //ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) //conteúdo do array permanece o mesmo
{
    var index := 0;
    i := 0;
    while index < a.Length
      invariant 0 <= index <= a.Length
      invariant 0 <= i < a.Length
      invariant forall j :: 0 <= j < index ==> a[j] <= a[i]
    {
        if a[index] > a[i]
        {
            i := index;
        }
        index := index + 1;
    }
}