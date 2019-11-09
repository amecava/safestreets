open util/boolean

sig FiscalCode{}
sig Username{}
sig Password{}

sig TimeStamp{}
sig Type{}
sig Picture{}

abstract sig User{}

sig LoggedUser extends User{
    fiscalCode: one FiscalCode,

    username: one Username,
    password: one Password,

    topUser: one Bool
}
{
    // Users are considered a TopUser if they upload more than 50 violations (scaled values for simplicity)
    topUser = True iff #{v: Violation | some r: Report | r in v.report and r.uploadedBy = this}  >= 2
}

sig Report {
    uploadedBy: one LoggedUser,
    timeStamp: one TimeStamp,
    position: one Street,
    type: set Type,
    picture: one Picture,
    plate: lone Plate,

    validReport: one Bool
}
{
    // Reports must have at least one violation type
    #type >= 1
}

sig Violation{
    committedBy: one Plate,
    report: set Report
}
{
    // Violations must have at least one Report associated to it
    #report >= 1
    // All Reports associated to a Violation must have the same license Plate of the Violation
    some r: Report | r in report and committedBy = r.plate
}

sig City {
    areasOfCity: set Area,

    isSafe: one Bool
}
{
    // A City is considered unsafe if there are at least 5 areas of that City that are considered unsafe (scaled values for simplicity)
    isSafe = False iff #{a: Area |  a in areasOfCity} >= 2
}

sig Area {
    ofCity: one City,
    streetsOfArea: set Street,


    isSafe: one Bool
}
{
    // An Area is considered unsafe if there are at least 5 streets of that area that are considered unsafe (scaled values for simplicity)
    isSafe = False iff #{s: Street |  s in streetsOfArea} >= 2
}

sig Street {
    ofArea: one Area,

    isSafe: one Bool
}
{
    // A Street is considered unsafe if there are at least 10 violations on that Street (scaled values for simplicity)
    isSafe = False iff #{v: Violation | some r: Report | r in v.report and r.position = this}  >= 2
}

sig Plate {
    egregiousOffender: one Bool
}
{
    // A plate (representing a driver) becomes an "egregious offender" if the number of violations associated to its plate number becomes greater than 10 (scaled values for simplicity)
    egregiousOffender = True iff #{v: Violation | v.committedBy = this}  >= 2
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////

// All FiscalCodes have to be associated to a User 
fact FiscalCodeUserConnection {
    all f: FiscalCode | some l: LoggedUser | l.fiscalCode = f
}

// All Usernames have to be associated to a User 
fact UsernameUserConnection {
    all u: Username | some l: LoggedUser | l.username = u
}

// All Passwords have to be associated to a User 
fact PasswordUserConnection {
    all p: Password | some l: LoggedUser | l.password = p
}

// All TimeStamps have to be associated to a Report 
fact TimeStampReportConnection {
    all t: TimeStamp | some r: Report | r.timeStamp = t
}

// All Types have to be associated to a Report 
fact TypeReportConnection {
   all t: Type | some r: Report | r.type = t
}

// All Pictures have to be associated to a Report
fact PictureReportConnection {
    all p: Picture | some r: Report | r.picture = p
}

// All Areas have to be associated to a City
fact AreaCityConnection {
    all a: Area | some c: City | a in c.areasOfCity and a.ofCity = c
}

// All Streets have to be associated to an Area
fact StreetAreaConnection {
    all s: Street | some a: Area | s in a.streetsOfArea and s.ofArea = a
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////

// There must not be two different users with the same fiscal code
fact NoDoubleFiscalCode {
   no disjoint u1, u2: LoggedUser | u1.fiscalCode = u2.fiscalCode
}

// There must not be two different user with the same username
fact NoDoubleUsername {
    no disjoint u1, u2: LoggedUser | u1.username = u2.username
}

// There must not be two different Areas with the same Street
fact NoSameStreetInDifferentAreas {
    no disj a1, a2: Area | some s: Street | s in a1.streetsOfArea and s in a2.streetsOfArea
}

// There must not be two different Cities with the same Area
fact NoSameAreaInDifferentCities {
    no disj c1, c2: City | some a: Area | a in c1.areasOfCity and a in c2.areasOfCity
}

// There must not be two different Violation with the same Report
fact NoSameReportInDifferentViolations {
    no disj v1, v2: Violation | some r: Report | r in v1.report and r in v2.report
}

// There must not be two different reports with the same picture
fact NoDoublePictures{
   no disjoint r1, r2: Report | r1.picture = r2.picture
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////

// A valid Report must have a Plate
fact ValidReportHasPlate {
    all r: Report |  r.validReport = True implies r.plate != none
}

// A valid report must be included in a Violation
fact ReportToViolation {
    all r: Report |  r.validReport = True iff some v: Violation | r in v.report
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Violation's Reports must be valid and have a Plate valid and coherent to the Violation one
assert ViolationReports {
    all v: Violation | some r: Report | r in v.report implies r.validReport = True and r.plate != none and v.committedBy = r.plate
}

check ViolationReports for 5

///////////////////////////////////////////////////////////////////////////////////////////////////////////

pred world1 {
    #LoggedUser = 2

    #Area = 1
    #Street = 2

    #Violation = 4

    some disj l1, l2: LoggedUser | some disj s1, s2: Street | some disj v1, v2, v3, v4: Violation | s1.ofArea = s2.ofArea
	and v1.report.uploadedBy = l1 and  v2.report.uploadedBy = l1 and  v3.report.uploadedBy = l1 and  v4.report.uploadedBy = l2
	and v1.report.position = s1 and  v2.report.position = s1 and v3.report.position = s2 and  v4.report.position = s2
	
}

run world1 for 5
