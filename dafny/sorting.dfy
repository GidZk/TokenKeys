class Sorted {


//------------- 1a -------------

//solution 1

predicate Sorted( a: array<int>)
	requires a != null;

reads a;
{
 forall i : int :: 0 <= i < a.Length-1 ==> a[i] < a[i+1]
}



// ------------- 1b -------------

// solution 2

predicate Sorted2(a : array<int>)
	requires a != null;

reads a;
{

forall i , j : int :: 0 <= i < j < a.Length ==> a[i]< a[j]

}



// -------------   2a   -------------
/*
ghost method Sortedlol(a : array<int>)
	requires a != null;
	requires a.Length >= 2;

  ensures Sorted(a) ==> Sorted2(a)
{
}
*/
ghost method Sortedlol2(a : array<int>)

	requires a != null;
	requires  a.Length >= 2;
  	ensures Sorted2(a) ==> Sorted(a)
{
}


// -------------   2b   ------------- PAPER


// -------------   3a   -------------


}