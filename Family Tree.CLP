;-------------------------------------------------------------------------------------------------------
;----------------------------- defining templates for all the relationships ----------------------------
;-------------------------------------------------------------------------------------------------------

(deftemplate father-of (slot child) (slot father))
(deftemplate mother-of (slot child) (slot mother))
(deftemplate parent-of (slot child) (slot parent))
(deftemplate aunt-of (slot neice-or-nephew) (slot aunt))
(deftemplate uncle-of (slot neice-or-nephew) (slot uncle))
(deftemplate sibling-of (slot sibling1) (slot sibling2))
(deftemplate arebrothers (slot brother1) (slot brother2))
(deftemplate arebrothersister (slot brother) (slot sister))
(deftemplate aresisters (slot sister1) (slot sister2))
(deftemplate arehusbandwife (slot husband) (slot wife))
(deftemplate neice-of (slot neice) (slot uncle-or-aunt))
(deftemplate nephew-of (slot nephew) (slot uncle-or-aunt))
(deftemplate arecousins (slot cousin1) (slot cousin2))
(deftemplate grandfather-of (slot grandchild) (slot grandfather))
(deftemplate grandmother-of (slot grandchild) (slot grandmother))
(deftemplate greataunt-of (slot person) (slot greataunt))
(deftemplate greatuncle-of (slot person) (slot greatuncle))
(deftemplate greatgrandmother-of (slot person) (slot greatgrandmother))
(deftemplate greatgrandfather-of (slot person) (slot greatgrandfather))
(deftemplate male (slot person))
(deftemplate female (slot person))
(deftemplate stepparent-of (slot stepparent) (slot stepchild))
(deftemplate halfsibling-of (slot halfsibling1) (slot halfsibling2))

;-------------------------------------------------------------------------------------------------------
;--------------- Defining Facts which only includes parent-child relationship and gender ---------------
;-------------------------------------------------------------------------------------------------------


;-------------- Defining facts about who is the parent and who is the child  --------
;------------------------ That also includes step parent ----------------------------

(deffacts parents
(stepparent-of (stepparent john) (stepchild sam))
(stepparent-of (stepparent michelle) (stepchild joe))
(parent-of (child sam) (parent michelle))
(parent-of (child theodore) (parent amelia))
(parent-of (child theodore) (parent asher))
(parent-of (child charlotte) (parent amelia))
(parent-of (child charlotte) (parent asher))
(parent-of (child jasper) (parent amelia))
(parent-of (child jasper) (parent asher))
(parent-of (child jack) (parent theodore))
(parent-of (child jack) (parent cora))
(parent-of (child mary) (parent theodore))
(parent-of (child mary) (parent cora))
(parent-of (child isla) (parent theodore))
(parent-of (child isla) (parent cora))
(parent-of (child tom) (parent joe))
(parent-of (child harry) (parent joe))
(parent-of (child ron) (parent joe))
(parent-of (child joe) (parent john))
(parent-of (child kurt) (parent john))
(parent-of (child joe) (parent mary))
(parent-of (child kurt) (parent mary)) 
(parent-of (child max) (parent kurt))
(parent-of (child kelly) (parent kurt)) 
(parent-of (child nick) (parent isla)) 
(parent-of (child jonas) (parent isla)) 
)

;------------------- Defining facts of gender of people --------------------
(deffacts gender
(male (person sam))
(male (person max))
(male (person theodore))
(male (person jack))
(male (person john))
(male (person kurt))
(male (person joe))
(male (person tom))
(male (person harry))
(male (person ron))
(male (person nick))
(male (person jonas))
(male (person  asher))
(male (person  jasper))
(female (person  amelia))
(female (person  charlotte))
(female (person cora))
(female (person mary))
(female (person isla))
(female (person kelly))
(female (person michelle))
)


;---------------------------------- Defining rule for father ---------------------------------------
;-----If the person is a parent of a child and is male then he is his/her father -------------------

(defrule setfather
(declare (salience 100))
(parent-of (child ?c) (parent ?p))                            	; searching all the facts for parent and child relationship
(male (person ?p))					      	; For each fact found look if the parent is male 
=>
(assert(father-of (child ?c) (father ?p)))                    	; if all L.H.S conditions are true assign the parent as father of child.
)
;----------------------------------------------------------------------------------------------------

;--------------------------------- Defining rule for mother -----------------------------------------
;-----If the person is a parent of a child and is female then she is his/her mother -------------------


(defrule setmother
(declare (salience 99))
(parent-of (child ?c) (parent ?p))                            	; searching all the facts for parent and child relationship
(female (person ?p))                                          	; For each fact found look if the parent is female 
=>
(assert(mother-of (child ?c) (mother ?p)))			; if all L.H.S conditions are true assign the parent as father of child.
)
;-------------------------------------------------------------------------------------------------------


;--------------------------------- Defining rule for grandfather ---------------------------------------
;------- Finds the father of the parent of the child and assigns him childs grandfather ------------


(defrule setgrandfather
(declare (salience 98))
(or(father-of (child ?c1) (father ?f1))(mother-of (child ?c1) (mother ?f1))) 	; Seraching all facts for father or mother of a child
(father-of (child ?f1) (father ?f2))						; Searching for father of child's parent(mother and father).
=>
(assert(grandfather-of (grandchild ?c1) (grandfather ?f2)))			; Assigns the relationship of grandfather between child and grandfather
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- Defining rule for grandmother ---------------------------------------
;------- Finds the mother of parent of the child and assigns him childs grandfather ----------------

(defrule setgrandmother
(declare (salience 97))
(or(father-of (child ?c1) (father ?f1))(mother-of (child ?c1) (mother ?f1)))	; Seraching all facts for father or mother of a child
(mother-of (child ?f1) (mother ?f2))						; Searching for mother of child's parent(mother and father). 
=>
(assert(grandmother-of (grandchild ?c1) (grandmother ?f2)))			; Assigns the relationship of grandmother between child and grandmother
)

;-------------------------------------------------------------------------------------------------------


;--------------------------------- Defining rule for siblings ------------------------------------------
;------------------ If two child have same parent and then they are siblings ---------------------------

(defrule setsiblings
(declare (salience 91))
(parent-of (child ?c1) (parent ?p)) 						; Search for child1 with a same parent
(parent-of (child ?c2) (parent ?p))						; Search for child2 with a same parent	
;(!= ?c1 ?c2)									; This code if to reduce the redundancy of same person being declared as sibling. But currently i have defined another rule to reduce this redunddancy (rule with salience 90)
=>
(assert(sibling-of (sibling1 ?c1) (sibling2 ?c2)))				; Assign both the children as siblings
)

;-------------------------------------------------------------------------------------------------------


;------------------------------- defining rule to remove same person as sibling --------------------------
;---------------------- Here i assume that two sibling's would not have same name ------------------------
;------------------------------------------------- NOTE --------------------------------------------------
; Here we are only retracting facts with same person as sibling, there are still some redundant facts 
; woth two same siblings have alternate position in facts. for eg ; (sibling-of (sibling1 Aron) (sibling2 Naina))
; and (sibling-of (sibling1 Naina) (sibling2 Aron)).This additional facts are retracted last once
; all three direct relationships 1. arebrothersister 2. arebrothers 3. aresister are built.

(defrule removeredundantsiblings
(declare(salience 90))
?v <- (sibling-of (sibling1 ?name) (sibling2 ?name)) 	; Find facts defining same person as his sibling and store it in variable v
=>
(retract ?v)						; remove the fact rom knowledge-base
)

;-------------------------------------------------------------------------------------------------------


;----------------------------------------- defining rule for brothers ----------------------------------
;------------------------ Assumption: If two siblings are male the are Brothers ------------------------
;------------------------------------------------- NOTE --------------------------------------------------
; Here we are using redundant siblings facts and because of that we dont have to check for the possiblities 
; second person being of other gender.

(defrule setbrothers
(declare (salience 89))
(sibling-of (sibling1 ?c1) (sibling2 ?c2))		; Finds siblings from facts
(male (person ?c1))					; check if first person is male 
(male (person ?c2))					; check if second person is male
=>
(assert(arebrothers (brother1 ?c1) (brother2 ?c2)))     ; derived that both of them are brothers
)

;-------------------------------------------------------------------------------------------------------

;----------------------------------------- defining rule for sisters ----------------------------------
;------------------------ Assumption: If two siblings are female the are Sisters ------------------------
;------------------------------------------------- NOTE --------------------------------------------------
; Here we are using redundant siblings facts and because of that we dont have to check for the possiblities 
; second person being of other gender.

(defrule setsisters
(declare (salience 88))
(sibling-of (sibling1 ?c1) (sibling2 ?c2))		; Finds siblings from facts
(female (person ?c1))					; check if first person is female
(female (person ?c2))					; check if second person is female
=>
(assert(aresisters (sister1 ?c1) (sister2 ?c2)))        ; derive that both of them are sisters
)

;------------------------------------------------------------------------------------------------------

;----------------------------------------- defining rule for sisters ----------------------------------
;------ Assumption: If one sibling is male and other female then they are Brother and Sister ----------
;------------------------------------------------- NOTE --------------------------------------------------
; Here we are using redundant siblings facts and because of that we dont have to check for the possiblities 
; second person being of other gender.

(defrule setbrothersister
(declare (salience 87))
(sibling-of (sibling1 ?c1) (sibling2 ?c2))		; Finds siblings from facts
(male (person ?c1))					; check if first person is male
(female (person ?c2))					; check if second person is female
=>
(assert(arebrothersister (brother ?c1) (sister ?c2)))
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for husband and wife ----------------------------------
;------ Assumption: If they have a child, they are maried and so are husband and wife  -----------------

(defrule sethusbandwife
(declare (salience 86))
(or							

;---- find parents of a child

(and(father-of (child ?c) (father ?f))   		; find the father of the child
(mother-of (child ?c) (mother ?m)))			; find the mother of the child

;---- or find stepparent and parent of the child

(and (stepparent-of (stepparent ?f) (stepchild ?c))	; find the stepparent of the child
(parent-of (child ?c) (parent ?m))			; find the parent of child
(male (person ?f))					; finds who is the male parent
)
)
=>
(assert(arehusbandwife (husband ?f) (wife ?m)))         ; derived that they are husband and wife
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for uncle ---------------------------------------------
;--------------------------- Assumption: Brother of any parent is uncle   ------------------------------

(defrule setuncle
(declare (salience 85))
(or(father-of (child ?c) (father ?v))(mother-of (child ?c) (mother ?v)))	; Find the parent of child
(sibling-of (sibling1 ?v) (sibling2 ?u))					; Find the sibling of the parent
(male (person ?u))								; check if the sibling is male i.e. brother
=>
(assert(uncle-of (neice-or-nephew ?c) (uncle ?u)))				; derived that he is uncle of the child
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for aunt ---------------------------------------------
;--------------------------- Assumption: sister of any parent is aunt   ------------------------------

(defrule setaunt
(declare (salience 84))
(or(father-of (child ?c) (father ?v))(mother-of (child ?c) (mother ?v)))	; Find the parent of child
(sibling-of (sibling1 ?v) (sibling2 ?u))					; Find the sibling of the parent
(female (person ?u))								; check if the sibling is female i.e. sister
=>
(assert(aunt-of (neice-or-nephew ?c) (aunt ?u)))				; derived that she is aunt of the child
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for niece ---------------------------------------------
;-- Assumption: if the person is uncle or aunt of a child and the child is female she is niece   -------

(defrule setniece
(declare (salience 83))
	(or(uncle-of (neice-or-nephew ?n) (uncle ?v))(aunt-of (neice-or-nephew ?n) (aunt ?v))) 	; Find the niece/nephew of the person(uncle/aunt)
	(female (person ?n))									; If the niece/nephew is female she is niece		
=>
	(assert(neice-of (neice ?n) (uncle-or-aunt ?v)))					; derived that she is neice of the person
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for niece ---------------------------------------------
;-- Assumption: if the person is uncle or aunt of a child and the child is male he is nephew  ----------

(defrule setnephew
(declare (salience 82))
	(or(uncle-of (neice-or-nephew ?n) (uncle ?v))(aunt-of (neice-or-nephew ?n) (aunt ?v)))	; Find the niece/nephew of the person(uncle/aunt)
	(male (person ?n))									; If the niece/nephew is female she is niece	
=>
	(assert(nephew-of (nephew ?n) (uncle-or-aunt ?v)))					; derived that she is neice of the person
)

;-------------------------------------------------------------------------------------------------------


;--------------------------------- defining rule for cousin ---------------------------------------------
;----------------------- Assumption: child of aunt or uncle is cousin of the person  -------------------

(defrule setcousin
(declare (salience 81))
(or(uncle-of (neice-or-nephew ?n) (uncle ?v))(aunt-of (neice-or-nephew ?n)(aunt ?v)))  	; Find uncle or aunt of a person
(parent-of (child ?cousin) (parent ?v))							; Find the child of aunt or uncle
=>
(assert(arecousins (cousin1 ?n) (cousin2 ?cousin)))					; Derived that that the child is cousin of the person
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for greataunt -----------------------------------------
;----------------------- Assumption: Sister of grandparent is greataunt  -------------------------------

(defrule setgreataunt
(declare (salience 80))
(or(grandfather-of (grandchild ?c) (grandfather ?p))(grandmother-of (grandchild ?c) (grandmother ?p))) 	; find grandparent of person
(sibling-of (sibling1 ?p) (sibling2 ?a))								; find sibling of grandparent
(female (person ?a))											; check if sibling is sister
=>
(assert(greataunt-of (person ?c) (greataunt ?a)))							; derived that she is greataunt of the person
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for greatuncle -----------------------------------------
;----------------------- Assumption: Brother of grandparent is greatuncle -------------------------------

(defrule setgreatuncle
(declare (salience 79))
(or(grandfather-of (grandchild ?c) (grandfather ?p))(grandmother-of (grandchild ?c) (grandmother ?p)))	; find grandparent of person
(sibling-of (sibling1 ?p) (sibling2 ?u))								; find sibling of grandparent
(male (person ?u))											; check if sibling is brother
=>
(assert(greatuncle-of (person ?c) (greatuncle ?u)))							; derived that she is greatuncle of the person
)

;-------------------------------------------------------------------------------------------------------

;--------------------------------- defining rule for greatgrandmother -----------------------------------------
;----------------------- Assumption: Mother of grandparent is greatgrandmother -------------------------------


(defrule setgreatgrandmother
(declare (salience 78))
(or(grandfather-of (grandchild ?c) (grandfather ?p))(grandmother-of (grandchild ?c) (grandmother ?p))) 	; find grandparent of person
(mother-of (child ?p) (mother ?ggm))									; Find the mother of grandparent
=>
(assert(greatgrandmother-of (person ?c) (greatgrandmother ?ggm)))					; Derived that she is greatgrandmother of person
)

;-------------------------------------------------------------------------------------------------------


;--------------------------------- defining rule for greatgrandfather -----------------------------------------
;----------------------- Assumption: father of grandparent is greatgrandfather -------------------------------

(defrule setgreatgrandfather
(declare (salience 77))
(or(grandfather-of (grandchild ?c) (grandfather ?p))(grandmother-of (grandchild ?c) (grandmother ?p)))	; find grandparent of person
(father-of (child ?p) (father ?ggf))									; Find the father of grandparent
=>
(assert(greatgrandfather-of (person ?c) (greatgrandfather ?ggf)))					; Derived that he is greatgrandfather of person
)

;-------------------------------------------------------------------------------------------------------

;------------------------------ defining rule for halfsiblings -----------------------------------------
;-- Assumption: if stepparent of one child is parent of other and vice-versa, they are halfsiblings ----

(defrule sethalfsiblings
(declare (salience 76))
	(stepparent-of (stepparent ?p1) (stepchild ?c1))		; Find the stepparent of child1				
	(stepparent-of (stepparent ?p2) (stepchild ?c2))		; Find the stepparent of child2
	(parent-of (child ?c1) (parent ?p2))				; match the stepparent of child2 with parent of child1
	(parent-of (child ?c2) (parent ?p1))				; match the stepparent of child1 with parent of child2
=>
(assert(halfsibling-of (halfsibling1 ?c1) (halfsibling2 ?c2)))		; Derived that both are half-siblings
)
	
;-------------------------------------------------------------------------------------------------------


;-------------------------------------------------------------------------------------------------------
;---------------------------------------- Remove Redundancy --------------------------------------------
;-------------------------------------------------------------------------------------------------------

;------------ Remove all siblings facts as direct relationship as brother and sister are defined now----

(defrule removere_all_siblings
(declare(salience 50))
?v <- (sibling-of (sibling1 ?) (sibling2 ?))
=>
(retract ?v)
)


;------------------- Remove all redundant facts which defines same person as his brother ---------------

(defrule remove_same_person_as_brothers
(declare(salience 49))
?v <- (arebrothers (brother1 ?name) (brother2 ?name))
=>
(retract ?v)
)

;--------------------------- Remove all redundant facts which are just change in slot ------------------

(defrule remove_redundant_brothers
(declare(salience 47))
(arebrothers (brother1 ?name1) (brother2 ?name2))
?v <- (arebrothers (brother1 ?name2) (brother2 ?name1))
=>
(retract ?v)
)

;------------------- Remove all redundant facts which defines same person as her sister ---------------

(defrule remove_same_person_as_sisters
(declare(salience 48))
?v <- (aresisters (sister1 ?name) (sister2 ?name))
=>
(retract ?v)
)

;--------------------------- Remove all redundant facts which are just change in slot ------------------

(defrule remove_redundant_sisters
(declare(salience 46))
(aresisters (sister1 ?name1) (sister2 ?name2))
?v <- (aresisters (sister1 ?name2) (sister2 ?name1))
=>
(retract ?v)
)

;------------ Remove all siblings facts as direct relationship as father/mother are defined now----

(defrule remove_all_parent
(declare(salience 45))
?v <- (parent-of (child ?) (parent ?))
=>
(retract ?v)
)

;--------------------------- Remove all redundant facts which are just change in slot ------------------

(defrule remove_redundant_cousins
(declare(salience 44))
(arecousins (cousin1 ?name1) (cousin2 ?name2))
?v <- (arecousins (cousin1 ?name2) (cousin2 ?name1))
=>
(retract ?v)
)

;--------------------------- Remove all redundant facts which are just change in slot ------------------


(defrule remove_redundant_halfsiblings
(declare(salience 43))
(halfsibling-of (halfsibling1 ?name1) (halfsibling2 ?name2))
?v <- (halfsibling-of (halfsibling1 ?name2) (halfsibling2 ?name1))
=>
(retract ?v)
)



