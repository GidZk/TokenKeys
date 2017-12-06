datatype clearanceLevel = Low | Medium | High

class Token {

    var valifyer : bool
	var security_level : clearanceLevel;
	var user_ID	: int
	


constructor (id : int, sec_lvl : clearanceLevel)
requires id >= 0 	// users always a positive integer
ensures 		valifyer 
			&&  user_ID == id 
			&&  security_level == sec_lvl
{

valifyer := true;
security_level := sec_lvl;
user_ID := id;
}


/*
requires : that this current token already is valid
ensures  : that the current token is invalid
*/

method invalidateToken()
modifies this`valifyer
requires valifyer == true
ensures valifyer == false 
{

valifyer := false;

}

}




//================================= Class User  ===========================================


class User{
	var user_ID  	: int 
	var token 		: Token

	constructor(uID : int)
    requires uID > 0
	 ensures uID == uID
	{
		user_ID := uID;
	}

/*
	method enroll()
	requires token != null
	ensures token.user_ID == user_ID
	{

*/


	}



//================================= Class Enrolmmentsys  ===========================================


class EnrollmentSystem{
  var maxUsers : int;
  var userMap : map< int, Token>;

	constructor(maxU : int)
  requires maxUsers > 0
  ensures maxUsers == maxU
  ensures |userMap| == 0
  {
    maxUsers := maxU;
    userMap :=map[];
  }


}











