//p 
while(q)
	//invariant r
	//decrease measure m
{
	//assume q && r
	...
	...
	//prove r && m < (m at the top of the loop)
}
// !q && r 

/*
 *	Binary search
 */
size_t bs_find(int *p, size_t len, int v)
-may not require: forany size_t i,j: i <= j < len => p[i] <= p[j]
-ensure: 0 <= \r <= len
-ensure: forany size_t i: i < \r => p[i] < v
-ensure: \r == len || p[\r] >= v
{
	size_t x = 0, y = len;
	while(x != y)
	// inv: x <= y <= len
	// inv: forany size_t i: i < x => p[i] < v
	// inv: y == len || p[y] >= v
	{
		size_t m = x + (y - x)/2;
		if (p[m] < v)
		{
			/* let y-x decrease */
			x = m + 1;
		} else {
			y = m;
		}
	}
	return x;
}

/*
 *	Partition
 */
void partition(int* p, size_t len, int v)
-ensure: exist size_t x,z: (x <= z <= len) and (forany size_t i: i < x ? p[i] < v:
																 i < z ? p[i] == v:
																 i < len ? p[i] > v:
																 true)
{
	// inv: forany size_t x, y, z: (x <= y <= z <= len) and (forany size_t i: i < x ? p[i] < v:
	//																		  i < y ? p[i] == v:
	//																		  i < z ? true:
	//																		  i < len? p[i] > v:
	//																		  true)
	size_t x = 0, y = 0, z = len;
	while(y != z)
	{
		//range [y, z) is unknown
		if (p[y] < 0)
		{
			swap(p+x, p+y);
			++x;
			++y;
		}else if (p[y] == 0)
		{
			++y;
		}else {
			--z;
			swap(p+y, p+z);
		}
	}
}

/*
 *	Insertion sort
 */
void sort(int* p, size_t len)
-ensure: forany size_t i, j: i <= j < len => p[i] <= p[j]
{
	//inv: forany size_t i, j: i <= j < u => p[i] <= p[j]
	//inv: forany size_t i, j: (i <= j <= u and j != v) => p[i] < p[j]
	for (size_t u = 0; u < len;)
	{	
		for (size_t v = ++u; v > 0 && p[v] < p[v-1]; swap(p+v, p+v-1), v--)
		{
			
		}
	}
}

/*
 *	Bubble sort
 */
void sort(int* p, size_t len)
-ensure: forany size_t i, j: i <= j < len => p[i] <= p[j]
{
	//inv: forany size_t i, j: i <= j < u => p[i] <= p[j]
	//inv: forany size_t i, j: (i <= j < len and i < u) => p[i] <= p[j]
	for (int u = 1; u < len; ++u)
	{
		i = u - 1;
		for (int j = u; j < len; ++j)
		{
			if (p[i] > p[j])
			{
				swap(p+i, p+j);
			}
		}
	}
}

/*
 *	Selection sort
 */
void sort(int* p, size_t len)
-ensure: forany size_t i, j: i <= j < len => p[i] <= p[j]
{
	//inv: forany size_t i, j: i <= j < u => p[i] <= p[j]
	//inv: forany size_t i, j: (i <= j < len and i < u) => p[i] <= p[j]
	for (int u = 0; u < len; ++u)
	{
		int i = u;
		int v = p[u];
		for (int j = u + 1; j < len; ++j)
		{
			if (v > p[j])
			{
				i = j;
				v = p[j];
			}
		}
		swap(p+u, p+i);
	}
}