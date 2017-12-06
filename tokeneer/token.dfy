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

