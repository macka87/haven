/* *****************************************************************************
 * Project Name: Hardware - Software Framework for Functional Verification 
 * File Name:    C Scoreboard Transaction Table 
 * Description: 
 * Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
 * Date:         3.5.2011 
 * ************************************************************************** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <err.h>
#include "dpi_tr_table_pkg.h"

typedef struct ListNode {
	size_t size;
	unsigned char* data;
	struct ListNode* next;
	struct ListNode* prev;
} TListNode;

//-----------------------------------------------------------------------------
//- GLOBAL VARIABLES
//-----------------------------------------------------------------------------
static TListNode* scoreboard_front = NULL;
static TListNode* scoreboard_end   = NULL;
int added = 0;
int removed = 0;

//-----------------------------------------------------------------------------
//- USER Functions
//-----------------------------------------------------------------------------

/*
 *  Trasaction is added to scoreboard table implemented as list in C language. 
 */
void c_addToTable(const svOpenArrayHandle inTrans){

	TListNode* newList = malloc(sizeof(TListNode));
	newList->size = svSize(inTrans, 1);
	newList->data = malloc(newList->size);
	memcpy(newList->data, svGetArrayPtr(inTrans), newList->size);
	newList->next = NULL;

	if (scoreboard_front == NULL){	
    // list is empty
		newList->prev = NULL;
		scoreboard_front = newList;
		scoreboard_end = newList;
		added++; 
	}
	else{
		newList->prev = scoreboard_end;
		scoreboard_end->next = newList;
		scoreboard_end = newList;
		added++;
	}
}

/*
 *  Checking emptiness of the transaction table.  
 */
 int c_tableEmpty(){
   return !scoreboard_front;
 }

/*
 *  Transaction is removed from scoreboard table after comparation. If any 
 *  discrepancy occures, error message is printed on screen and verification
 *  stops.  
 */
int c_removeFromTable(const svOpenArrayHandle outTrans){
  unsigned int len;       // length of received data
  unsigned char *auxPkt;  // pointer to received data
  
  len = svSize(outTrans, 1);
  auxPkt = (unsigned char*) svGetArrayPtr(outTrans);
  
	if (scoreboard_front == NULL){
	  printf("Scoreboard empty!!!!!!!!!!!!!\n");
		return EXIT_FAILURE;
	}
	else{
	  TListNode* node = scoreboard_front;
	  scoreboard_front = node->next;

		if (scoreboard_front == NULL){
		  scoreboard_end = NULL;
		}
		else{
		  scoreboard_front->prev = NULL;
		}

		if (len != node->size){
		  printf("Size doesn't match!!!!!!!!!!!!!\n");
			return EXIT_FAILURE;
		}
		else{
		  if (memcmp(node->data, auxPkt, len)){
			  printf("Data don't match!!!!!!!!!!!!!\n");
			  return EXIT_FAILURE;
		  }
		}
    free(node);
    removed++;
	}
  return EXIT_SUCCESS;
} 

/*
 *  Display final state of transaction table. 
 */
void c_displayTable(){
  printf("------------------------------------------------------------\n");
  printf("-- C TRANSACTION TABLE\n");
  printf("------------------------------------------------------------\n");
  printf("Items added: %d\n", added);
  printf("Items removed: %d\n", removed);
  printf("\n");
}
