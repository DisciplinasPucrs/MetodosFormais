datatype ArvBin<T> = Vazia | Nodo(esq:ArvBin<T>, x:T, dir:ArvBin<T>)

function tamanho<T>(a:ArvBin<T>):nat
{
    match a
    case Vazia => 0
    case Nodo(e,x,d) => 1 + tamanho(e) + tamanho(d)
}

function tamanhoEsquerda<T>(a:ArvBin<T>):nat
{
    match a
    case Vazia => 0
    case Nodo(e,_,_) => 1 + tamanhoEsquerda(e)
}

method Main()
{
    var arv1: ArvBin<nat> := Vazia;
    assert tamanho(arv1) == 0;
    var arv2 := Nodo(Nodo(Vazia,2,Vazia),1,Vazia);
    assert tamanho(arv2) == 2;
}
