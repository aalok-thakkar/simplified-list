struct xlist;

struct listitem {

	char value;
	struct listitem *next;
	struct listitem *prev;
	struct xlist *container;
	
};

struct xlist {
	int length;
	struct listitem * index;
	struct listitem end;
	
};

/*@ predicate listitem(struct listitem *item, char value, struct listitem *next, struct listitem *prev, struct xlist *container) = 
	item->value |-> value &*&
	item->next |-> next &*&
	item->prev |-> prev &*&
	item->container |-> container &*&
	next == item ?
		true
		:
		listitem(next, _, _, item, container) &*&
		listitem(prev, _, item, _, container);
	

predicate linearize(struct listitem *first, struct listitem *end, list<struct listitem *> lambda) =
	first == end ?
		lambda == nil
		:
		first->next |-> ?fnext &*& //l use listitem predicate
		fnext->prev |-> first &*&
		lambda == cons(first, ?lambda2) &*&
		linearize(fnext, end, lambda);

predicate list(struct xlist *list, list<struct listitem *> lambda) =
	list->index |-> _ &*&
	list->length |-> _ &*&
	listitem(&(list->end), 127, ?first, _, list) &*&
	linearize(first, &(list->end), lambda);
@*/


void list_initialise(struct xlist *list)
	//@ requires list(list, _);
	//@ ensures list(list, nil);
{
	//@ open list(list, _);
	//@ open listitem(?end, _, _, _, _);
	list->index = &(list->end);
	list->end.value = 127;

	list->end.next = &(list->end);
	list->end.prev = &(list->end);
	
	list->length = 0;
	//@ close linearize(end, end, nil);
	//@ close listitem(end, 127, end, end, list);
	//@ close list(list, nil);
}

void listitem_initialize(struct listitem * item)
	//@ requires listitem(item, ?value, ?next, ?prev, _);
	//@ ensures listitem(item, value, next, prev, 0);
{
	//@ open listitem(item, value, next, prev, _);
	item->container = 0;
	//@close listitem(item, value, next, prev, 0);
}

int list_remove(struct listitem *item)
	//@ requires listitem(item, ?value, _, _, ?container) &*& list(container, _);
	//@ ensures true;
{
	//@ open listitem(item, value, ?prev, ?next, container);
	struct xlist *list = item->container;

	//@ open listitem(prev, _, _, _, _);
	item->next->prev = item->prev;
	item->prev->next = item->next;

	if(list->index == item)
	{
		list->index = item->prev;
	}

	item->container = 0;
	(list->length)--;

	return list->length;
}

void list_insert(struct xlist *list, struct listitem *item)
{
	struct listitem *iter;
	char insert_value = item->value;

	if(insert_value == 127)
	{
		iter = list->end.prev;
	}
	else
	{
		for(iter = &(list->end); iter->next->value <= insert_value; iter = iter->next){}
	}

	item->next = iter->next;
	item->next->prev = item;
	item->prev = iter;
	iter->next = item;

	item->container = list;

	(list->length)++;
}

main()
 {
     return 0;
 } 
