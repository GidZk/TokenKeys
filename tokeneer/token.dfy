datatype clearanceLevel = Low | Medium | High

class Token {

    var valifyer : bool;
	var clearance_level : clearanceLevel;
	var user_ID	: int;
	


method INIT (id : int, sec_lvl : clearanceLevel)
modifies this`valifyer
modifies this`user_ID
modifies this`clearance_level
requires id >= 0 	// users always a positive integer
ensures 		valifyer 
			&&  user_ID == id 
			&&  clearance_level == sec_lvl
{
clearance_level := sec_lvl;
user_ID := id;
valifyer := true;
}



/*
requires : that this current token already is valid
ensures  : that the current token is invalid
*/

method invalidateToken()
modifies this`valifyer
requires  valifyer
ensures  !valifyer 
{

valifyer := false;
}

}




//================================= Class User  ===========================================


class User{
	var token 		: Token

	method INIT()
	modifies this`token
	ensures token == null	
	{
		token := null;

	}


	}


//================================= Class Enrolmmentsys  ===========================================


class EnrollmentSystem{

var idCounter : int;
var userSet : set<int>;

predicate Valid_Enrollment()
reads this`idCounter
reads this`userSet
{
	 0 <= idCounter 

}


method INIT()
	modifies this`idCounter
	modifies this`userSet
		ensures userSet == {} && |userSet| == 0 
		ensures idCounter == 0 
  {
    userSet := {};
    idCounter := 0;
  }

method register(user : User, cl : clearanceLevel)
	modifies this`userSet
	modifies this`idCounter
	modifies user`token, user.token
		requires user != null
		requires 	Valid_Enrollment()
		ensures 	Valid_Enrollment()
		ensures old(idCounter)  == idCounter - 1 
		{

			userSet := userSet + {idCounter};
			// write method for this
			user.token  := new Token.INIT(idCounter, cl);
			idCounter := idCounter + 1;

		}





}









