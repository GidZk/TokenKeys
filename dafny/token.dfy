datatype ClearanceLevel = Low | Medium | High

class Token {

	var valifyer : bool
	var security_level : ClearanceLevel;
	var user_ID	: int
	


constructor (id, secLvl)
modifies this`id, this.security_level, this`valifyer
requires user > 0 	// users always a positive integer

ensures 	valifyer 				&& 
			user_ID 		== id 	&&
			security_level 	== secLvl
{

valifyer := true
security_level :secLvl
user_ID :=id

}



}

