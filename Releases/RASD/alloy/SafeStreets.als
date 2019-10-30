open util/boolean

abstract sig User{}

sig LoggedUser extends User{
    fiscalCode: one String,
    username: one String,
    password: one String
}

sig GuestUser extends User{
    userId: one String
}

sig Violation{

}

sig Position {

} 

sig GIS {

}

sig Municipality {

}




