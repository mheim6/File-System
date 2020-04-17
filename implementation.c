/*
	Monica Heim .
	Operating Systems Homework 4
	December 5,2019
	MyFS: a tiny file-system written for educational purposes

	MyFS is

	Copyright 2018-19 by

	University of Alaska Anchorage, College of Engineering.

	Contributors: Christoph Lauter
				... and
				Monica Heim

	and based on

	FUSE: Filesystem in Userspace
	Copyright (C) 2001-2007  Miklos Szeredi <miklos@szeredi.hu>

	This program can be distributed under the terms of the GNU GPL.
	See the file COPYING.

	gcc -Wall myfs.c implementation.c `pkg-config fuse --cflags --libs` -o myfs

*/

#include <stddef.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>
#include <time.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>
#include <time.h>
#include <stdint.h>


#define path_separator ("/")                       
#define dir_separator (":")                       
#define num_of_end ("\n")                        
#define m_init_number_block (UINT32_C(0xdeadd0c5))   


typedef struct Handler {
		uint32_t memInit;                     
		size_t bytesDis;                      
		size_t inoCount;                  
		size_t membCount;               
		struct Inode *inodePTR;           
		struct memHeader *membPTR;            
} Handler;  

typedef struct memHeader {
		int *memblck_occupied;                     
		size_t *datasize_occup;              
		size_t *nextOffset;             
																				
} memHeader;


typedef struct Inode { 
		char name[256];                     
		int *dirFile_check;                   
		int *subdir_count;                       
		size_t *data_size_bytes;                
		struct timespec *last_accessTime;          
		struct timespec *last_time_modified;          
		size_t *fileptr_offset;            
																				
} Inode;



static Inode* datasize_occup(Handler *fs, const char *path);


#define handlerSize sizeof(Handler) 
#define i_node_full_size sizeof(Inode)
#define memory_header_size sizeof(memHeader)
#define data_input (4 * 1024 - sizeof(memHeader))    
#define memorybSize sizeof(memHeader) + data_input
#define minFSsize sizeof(Handler) + sizeof(Inode) + (2 * memorybSize) 
#define startOffset sizeof(Handler)


static void* memb_data_ptr(Handler *fs, memHeader *memblock){
		return (void*)(memblock + memory_header_size);
}

static void* mem_ptr(Handler *fs, size_t *offset) {
		return (void*)((long unsigned int)fs + (size_t)offset);
}

// Returns 1 if given bytes are alignable on the given block_sz, else 0.
int align_check(size_t bytes, size_t block_sz) {
		if (bytes % block_sz == 0)
				return 1;
		return 0;
}
size_t kb_convert(size_t size) {
		return (size * 1024);
}
int kb_align_check(size_t kbs_size, size_t block_sz) {
		return align_check(kb_convert(kbs_size), block_sz);
}

static size_t mem_offset(Handler *fs, void *ptr) {
		return ptr - (void*)fs;
}
size_t byte_convert(size_t size) {
		return (1.0 * size / 1024);
}


static int if_memb_free(memHeader *memhead) {
		if (memhead->memblck_occupied == 0)
				return 1;
		return 0;
}

static memHeader* memblock_nextfree(Handler *fs) {
		memHeader *memblock = fs->membPTR;
		size_t membCount = fs->membCount;

		for (int i = 0; i < membCount; i++)
		{
				if (if_memb_free(memblock))
						return memblock;

				memblock = (memHeader*)((size_t)memblock + memorybSize);
		}
		return NULL;
}

static size_t num_of_free(Handler *fs) {
		Inode *inode = fs->inodePTR;
		size_t block_count = fs->membCount;
		size_t used_block_count = 0;
		size_t nodeB = 0;
		for (int i = 0; i < fs->inoCount; i++) {
				nodeB = *(size_t*)(&inode->data_size_bytes);

				if (nodeB % data_input > 0)
						used_block_count += 1;
				used_block_count += nodeB / data_input; // division
				inode++;
		}

		return block_count - used_block_count;
}

size_t pop_data(Handler *fs, memHeader *memhead, const char *buf) {
		memHeader *memblock = (memHeader*) memhead;
		size_t totalSize = 0;
		size_t prevSize = 0;
		size_t writeSize = 0;
		while (1) {
				prevSize = totalSize;
				writeSize = (size_t)memblock->datasize_occup;
				totalSize += writeSize;
				if (!writeSize) 
						break;  
				char *memblock_data_field = (char *)(memblock + memory_header_size);
				void *write_to_buf = (char *)buf + prevSize;
				memcpy(write_to_buf, memblock_data_field, writeSize);
				if (memblock->nextOffset == 0) 
						break;
				else
						memblock = (memHeader*)mem_ptr(fs, memblock->nextOffset);
		}
		return totalSize;
}

//last access time for the given node pointing now
static void set_access(Inode *inode, int set_modified) {
		if (!inode) return;

		struct timespec currTime;
		clock_gettime(CLOCK_REALTIME, &currTime);

		inode->last_accessTime = &currTime;
		if (set_modified)
				inode->last_time_modified = &currTime;
}

// Return 1 if the given inode is for a directory, if not it will return 0
static int is_directory(Inode *inode) {
		if (inode->dirFile_check == 0)
				return 0;
		else
				return 1;
}

// Return 1 unless ch an illigal naming char
static int inode_char_check(char ch) {
		return  (!(ch < 32 || ch == 44 || ch  == 47 || ch == 58 || ch > 122));
}

// Return 1 if name is legal ascii chars and length is appropriate
static int inode_name_check(char *name) {
		int len = 0;

		for (char *c = name; *c != '\0'; c++) {
				len++;
				if (len > 256) return 0;            
				if (!inode_char_check(*c)) return 0;   
		}

		if (!len) return 0;  // 0 length is not valid
		return 1;           
}


// Return 1 if passes succesfull and 0 if it fails
int inode_name_set(Inode *inode, char *name) {
		if (!inode_name_check(name))
				return 0;
		strcpy(inode->name, name); 
		return 1;
}

static memHeader* inode_first(Handler *fs, Inode *inode) {
		return (memHeader*)mem_ptr(fs, inode->fileptr_offset);
}

static int inode_isfree(Inode *inode) {
		if (inode->fileptr_offset == 0)
				return 1;
		return 0;
}

static Inode* inode_nextfree(Handler *fs) {
		Inode *inode = fs->inodePTR;

		for (int i = 0; i < fs->inoCount; i++) {
				if (inode_isfree(inode))
						return inode;
				inode++;
		}

		return NULL;
}


/*  iNode Helpers --------------------- */
/*  String Helpers -------------------- */


size_t str_len(char *arr) {
		int length = 0;
		for (char *c = arr; *c != '\0'; c++)
				length++;

		return length;
}

// Returns an index to the name element of the given path
static size_t str_name_offset(const char *path, size_t *pathlen) {
		char *begin, *temp, *next, *name;

		begin = next = strdup(path);    
		*pathlen = str_len(next);       
		next++;                         
		
		while ((temp = strsep(&next, path_separator)))
				if (!next)
						name = temp;

		size_t index = name - begin; 
		free(begin);

		return index;
}

//  represent the given number as string
static size_t find_length(size_t num) {
		int new_length = 0;

		while(num != 0) {
				new_length++;
				num /= 10;
		}

		return new_length;
}



/*  filesystem Helpers -------------- */


// Returns the root directory's inode for the given file system.
static Inode* find_root(Handler *fs) {
		return fs->inodePTR;
}

// Returns a handle to a filesystem of size systemSize onto fileptr.
static Handler* fs_init(void *fileptr, size_t size) {
		// Validate file system size
		if (size < minFSsize) {
				printf("ERROR: File system size too small.\n");
				return NULL;
		}

		// Map file system structure in the given memory space of machine
		Handler *fs = (Handler*)fileptr;

		size_t fs_size = size - startOffset;    
		void *beginning = fileptr + startOffset; 
		void *memb_beginning = NULL;                 
		int inodes_count = 0;                           
		int memb_count = 0;                        

		while (memb_count * data_input + inodes_count * i_node_full_size < fs_size) {
				inodes_count++;
				memb_count += 1;
		}
		
		memb_beginning = beginning + (i_node_full_size * inodes_count);		
		if (fs->memInit != m_init_number_block) {
				// Format
				memset(fileptr, 0, fs_size);				
				// fill in fs
				fs->memInit = m_init_number_block;
				fs->bytesDis = fs_size;
				fs->inoCount = inodes_count;
				fs->membCount = memb_count;
				fs->inodePTR = (Inode*) beginning;
				fs->membPTR = (memHeader*) memb_beginning;
				Inode *root_inode = find_root(fs);
				strncpy(root_inode->name, path_separator, str_len(path_separator));
				*(int*)(&root_inode->dirFile_check) = 1;
				*(int*)(&root_inode->subdir_count) = 0;
				fs->inodePTR->fileptr_offset = (size_t*) (memb_beginning - fileptr);
				*(int*)(&fs->membPTR->memblck_occupied) = 1;
				set_access(root_inode, 1);
		} 

		else {
				fs->bytesDis = fs_size;
				fs->inoCount = inodes_count;
				fs->membCount = memb_count;
				fs->inodePTR = (Inode*) beginning;
				fs->membPTR = (memHeader*) memb_beginning;
		}

		return fs;  
		// Returns handle to the file system
}


// Returns a handle to a myfs filesystem if it has success
static Handler *fs_handle(void *fileptr, size_t systemSize, int *errnoptr) {
		Handler *fs = fs_init(fileptr, systemSize);
		if (!fs && errnoptr) *errnoptr = EFAULT;
		return fs;
}

//  debug function.
static Inode *resolve_fspath(Handler *fs, const char *path, int *errnoptr) {
		// Ensure at least root dir symbol present
		if (strncmp(path, path_separator, 1) != 0) {
				*errnoptr = EINVAL;
				return NULL;                
		}

		Inode *inode = datasize_occup(fs, path);
		if (!inode && errnoptr) *errnoptr = ENOENT;
		return inode;
}



/*  iNode helpers ----------------------- */

static size_t data_to_buf(Handler *fs, Inode *inode, const char *buf) {
		set_access(inode, 0);
		return pop_data(fs, inode_first(fs, inode), buf);   
}

static void remove_data(Handler *fs, Inode *inode, int newblock) {
		memHeader *memblock = inode_first(fs, inode);
		memHeader *next_memb;     // ptr to memblock->nextOffset
		void *end_memb;         // End of memblock's data field

		 // Format each memblock
		do {
				next_memb = (memHeader*)mem_ptr(fs, memblock->nextOffset);
				end_memb = (void*)memblock + memorybSize;         // End of memblock
				memset(memblock, 0, (end_memb - (void*)memblock));  // Format memblock
				memblock = (memHeader*)next_memb;                     // Advance to next
				
		} while (next_memb != (memHeader*)fs);
		*(int*)(&inode->data_size_bytes) = 0;
		set_access(inode, 1);
		if (newblock)
				inode->fileptr_offset = 
						(size_t*)mem_offset(fs, memblock_nextfree(fs));
}

// Sets data field and updates size fields 
static void set_data(Handler *fs, Inode *inode, char *data, size_t file_data) {
		// If inode has existing data or no memblock associated.
		if (inode->data_size_bytes || inode->fileptr_offset == 0)
				remove_data(fs, inode, 1);
		memHeader *memblock = inode_first(fs, inode);
		if (file_data <= data_input) {
				void *data_field = memblock + memory_header_size;
				memcpy(data_field, data, file_data);
				*(int*)(&memblock->memblck_occupied) = 1;
				memblock->datasize_occup = (size_t*) file_data;
				memblock->nextOffset = 0;
		}
		else {
				size_t num_bytes = file_data;				
				char *data_index = data;
				memHeader *prev_block = NULL;
				size_t write_bytes = 0;				
				while (num_bytes) {
						if (num_bytes > data_input)
								write_bytes = data_input;           // More blocks yet needed
						else
								write_bytes = num_bytes;                // Last block needed
						char *data_write = memb_data_ptr(fs, memblock);
						memcpy(data_write, data_index, write_bytes);
						*(int*)(&memblock->memblck_occupied) = 1;
						*(size_t*)(&memblock->datasize_occup) = write_bytes;
						if (prev_block) 
								prev_block->nextOffset = 
										(size_t*)mem_offset(fs, (void*)memblock);
						prev_block = memblock;
						memblock->nextOffset = 0;				
						data_index += write_bytes;
						num_bytes = num_bytes - write_bytes; // Adjust num bytes to write
						memblock = memblock_nextfree(fs);    // Adavance to next free block
				}
		}
		set_access(inode, 1);
		inode->data_size_bytes = (size_t*) file_data;
}

// Appends the given data to the given Inode's current data 
static void append(Handler *fs, Inode *inode, char *append_data) {
		size_t data_size = 0;
		size_t append_sz = str_len(append_data);
		char *data = malloc(*(int*)(&inode->data_size_bytes) + append_sz);
		data_size = data_to_buf(fs, inode, data);
		size_t totalSize = data_size + append_sz;
		memcpy(data + data_size, append_data, append_sz);
		set_data(fs, inode, data, totalSize);
		free(data);
}


/*  Directory helpers -------------------- */

// Returns the inode for the given item 
static Inode* sub_node(Handler *fs, Inode *inode, char *name) {
		char *curr_data = malloc(*(int*)(&inode->data_size_bytes));
		data_to_buf(fs, inode, curr_data);
		char *elementptr = strstr(curr_data, name);
		if(elementptr == NULL) {
				free(curr_data);
				return NULL;
		}
		char *offset_ptr = strstr(elementptr, dir_separator);
		char *end_ptr = strstr(elementptr, num_of_end);
		if (!offset_ptr || !end_ptr) {
				printf("ERROR: Parse fail - Dir data may be corrupt -\n");
				free(curr_data);
				return NULL;
		}
		size_t offset;
		size_t offset_size = end_ptr - offset_ptr;
		char *offset_str = malloc(offset_size);
		memcpy(offset_str, offset_ptr + 1, offset_size - 1);  // +/- 1 excludes sep
		sscanf(offset_str, "%zu", &offset);                 // str to size_t
		Inode *subdir_inode = (Inode*)mem_ptr(fs, (size_t*)offset);
		// Cleanup
		free(curr_data);
		free(offset_str);		
		if (strcmp(subdir_inode->name, name) != 0)
				return NULL;        // fails
		return subdir_inode;    
}
// Creates a new sub-directory 
static Inode* create_directory(Handler *fs, Inode *inode, char *newdir) {
		if (!is_directory(inode)) {
				return NULL; 
		} 
		if (!inode_name_check(newdir)) {
				return NULL;
		}
		if(sub_node(fs, inode, newdir) != NULL) {
				return NULL;
		}
		Inode *newdir_inode = inode_nextfree(fs);
		memHeader *newdir_memblock = memblock_nextfree(fs);
		newdir_inode->fileptr_offset = (size_t*)mem_offset(fs, 
				(void*)newdir_memblock);
		if (newdir_inode == NULL || newdir_memblock == NULL) {
				printf("ERROR: Failed to get resources adding %s\n", newdir);
				return NULL;
		}
		size_t offset = mem_offset(fs, newdir_inode);        
		char offset_str[find_length(offset) + 1];      
		snprintf(offset_str, sizeof(offset_str), "%lu", offset);
		size_t data_size = 0;
		data_size = str_len(newdir) + str_len(offset_str) + 2; // +2 for : and \n
		char *data = malloc(data_size);
		strcpy(data, newdir);
		strcat(data, dir_separator);
		strcat(data, offset_str);
		strcat(data, num_of_end);
		append(fs, inode, data);		
		*(int*)(&inode->subdir_count) = *(int*)(&inode->subdir_count) + 1;		
		// Set new dir's properties
		inode_name_set(newdir_inode, newdir);
		*(int*)(&newdir_inode->dirFile_check) = 1;
		set_data(fs, newdir_inode, "", 0); 
		return newdir_inode;
}

// Removes the directory given inode from the file system.
static int remove_directory(Handler *fs, const char *path) {
		Inode *parent;
		Inode *child;
		char *parent_path, *begin, *temp, *next;
		begin = next = strdup(path);        // Duplicate path so we can manipulate
		next++;                             // Skip initial seperator
		parent_path = malloc(1);               // Init abs path str
		*parent_path = '\0';
		while ((temp = strsep(&next, path_separator))) {
				if (next) {
						parent_path = realloc(parent_path, str_len(parent_path) + str_len(temp) + 1);
						strcat(parent_path, path_separator);
						strcat(parent_path, temp);
				}
		}
		if (*parent_path == '\0')
				strcat(parent_path, path_separator);  // Path is root
		parent = datasize_occup(fs, parent_path);
		child = datasize_occup(fs, path);
		if (parent && child) {
				size_t dir_offset = mem_offset(fs, child);
				char offset_str[find_length(dir_offset) + 1];      
				snprintf(offset_str, sizeof(offset_str), "%lu", dir_offset);
				char *dir_name = strdup(child->name);
				size_t data_size = 0;
				data_size = str_len(dir_name) + str_len(offset_str) + 2;
				char *remoL = malloc(data_size);
				strcpy(remoL, dir_name);
				strcat(remoL, dir_separator);
				strcat(remoL, offset_str);
				strcat(remoL, num_of_end);
				char* main_data = malloc(*(int*)(&parent->data_size_bytes));
				size_t main_data_size = data_to_buf(fs, parent, main_data);
				size_t line_size = str_len(remoL);
				char *line_start = strstr(main_data, remoL);
				char *end_ptr = line_start + line_size;
				char *new_data = malloc(main_data_size - line_size);
				size_t temp_size1 =  line_start - main_data;
				size_t temp_size2 = main_data_size - temp_size1 - line_size;
				memcpy(new_data, main_data, temp_size1);
				memcpy(new_data + temp_size1, end_ptr, temp_size2);				
				set_data(fs, parent, new_data, temp_size1 + temp_size2);
				if (child->dirFile_check)
						*(int*)(&parent->subdir_count) = *(int*)(&parent->subdir_count) - 1;
				remove_data(fs, child, 0); 
				*(int*)(&child->dirFile_check) = 0;
				*(int*)(&child->subdir_count) = 0;
				free(parent_path);
				free(begin);
				free(remoL);
				free(dir_name);		
				return 1; // Success
		} else return 0; // Fail (nope)
}


/*  File helpers ----------------------- */


// makes a new file in the fs 
static Inode *create_file(Handler *fs, char *path, char *fname, char *data,
											 size_t data_size) {
		Inode *parent = datasize_occup(fs, path);

		if (!parent) {
				return NULL;
		}		
		if(sub_node(fs, parent, fname) != NULL) {
				printf("ERROR: File already exists\n");
				return NULL;
		}
		Inode *inode = inode_nextfree(fs);
		if (!inode) {
				printf("ERROR: Failed getting free inode for new file %s\n", fname);
				return NULL;
		}
		memHeader *memblock = memblock_nextfree(fs);
		if (!memblock) {
				printf("ERROR: Failed getting free memblock for new file %s\n", fname);
				return NULL;
		}
		if (!inode_name_set(inode, fname)) {
				printf("ERROR: Invalid file name\n");
				return NULL;
		}		
		size_t fileptr_offset = mem_offset(fs, (void*)memblock);
		inode->fileptr_offset = (size_t*)fileptr_offset;
		set_data(fs, inode, data, data_size);		
		size_t offset = mem_offset(fs, inode);
		char offset_str[find_length(offset) + 1];      
		snprintf(offset_str, sizeof(offset_str), "%zu", offset);
		size_t file_lookup = 0;
		file_lookup = str_len(fname) + str_len(offset_str) + 2; // +2 for : and \n
		char *flookup_data = malloc(file_lookup);
		strcpy(flookup_data, fname);
		strcat(flookup_data, dir_separator);
		strcat(flookup_data, offset_str);
		strcat(flookup_data, num_of_end);		
		append(fs, parent, flookup_data);
		free(flookup_data);
		return inode;
}
static Inode* datasize_occup(Handler *fs, const char *path) {
		Inode* root_dir = find_root(fs);
		if (strcmp(path, root_dir->name) == 0)
				return root_dir;
		Inode* curr_dir = root_dir;
		int curr_ind = 1;
		int path_ind = 0;
		int path_len = strlen(path);
		char curr_path_part[path_len];
		while (curr_ind < path_len) {
				path_ind = 0;
				while (1) {
						curr_path_part[path_ind] = path[curr_ind];
						curr_ind = curr_ind + 1;
						path_ind = path_ind + 1;
						if (path[curr_ind] == '/' || path[curr_ind] == '\0') {
								curr_ind = curr_ind + 1;
								break;
						}
				}
				curr_path_part[path_ind] = '\0';
				curr_dir = sub_node(fs, curr_dir, curr_path_part);
		}

		if (curr_dir && strcmp(curr_dir->name, curr_path_part) != 0)
				return NULL; // Path not found
		
		return curr_dir;
}

/* ----------------------------- */

/* -- __myfs_getattr_implem -- */
/* Implements the "stat" system call on the filesystem 
	 Accepts:
			fileptr       : ptr to the fs
			systemSize      : size of fs pointed to by fileptr
			errnoptr    : Error container
			uid         : User ID of file/dir owner
			gid         : Group ID of file/dir owner
			path        : Path of the file/dir in question
			stbuf       : Results container

	 Returns:
			-1  (w/error in *errnoptr) iff path not a valid file or directory. 
			Else returns 0 with file/dir info copied to stbuf as -
						nlink_t       Count of subdirectories (w/ . & ..), or just 1 if file)
						uid_t         Owners's user ID (from args)
						gid_t         Owner's group ID (from args)
						off_t         Real file size, in bytes (for files only)
						st_atim       Last access time
						st_mtim       Last modified time
						mode_t        File type/mode as S_IFDIR | 0755 for directories,
																						S_IFREG | 0755 for files
*/
int __myfs_getattr_implem(void *fileptr, size_t systemSize, int *errnoptr,
													uid_t uid, gid_t gid, const char *path, 
													struct stat *stbuf) {         
		Handler *fs = NULL;       
		Inode *inode = NULL;       
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		memset(stbuf, 0, sizeof(struct stat));
		stbuf->st_uid = uid;
		stbuf->st_gid = gid;
		stbuf->st_atim = *(struct timespec*)(&inode->last_accessTime); 
		stbuf->st_mtim = *(struct timespec*)(&inode->last_time_modified);    		
		if (inode->dirFile_check) {
				stbuf->st_mode = S_IFDIR | 0755;
				stbuf->st_nlink = *(int*)(&inode->subdir_count) + 2;  // "+ 2" for . and .. 
		} else {
				stbuf->st_mode = S_IFREG | 0755;
				stbuf->st_nlink = 1;
				stbuf->st_size = *(int*)(&inode->data_size_bytes);
		} 

		return 0;  // Success  
}
/* -- __myfs_readdir_implem -- */
/* Implements an emulation of the readdir system call on the filesystem 
	 of size systemSize pointed to by fileptr. 

	 If path can be followed and describes a directory that exists and
	 is accessable, the names of the subdirectories and files 
	 contained in that directory are output into *namesptr. The . and ..
	 directories must not be included in that listing.

	 If it needs to output file and subdirectory names, the function
	 starts by allocating (with calloc) an array of pointers to
	 characters of the right size (n entries for n names). Sets
	 *namesptr to that pointer. It then goes over all entries
	 in that array and allocates, for each of them an array of
	 characters of the right size (to hold the i-th name, together 
	 with the appropriate '\0' terminator). It puts the pointer
	 into that i-th array entry and fills the allocated array
	 of characters with the appropriate name. The calling function
	 will call free on each of the entries of *namesptr and 
	 on *namesptr.

	 The function returns the number of names that have been 
	 put into namesptr. 

	 If no name needs to be reported because the directory does
	 not contain any file or subdirectory besides . and .., 0 is 
	 returned and no allocation takes place.

	 On failure, -1 is returned and the *errnoptr is set to 
	 the appropriate error code. 

	 The error codes are documented in man 2 readdir.

	 In the case memory allocation with malloc/calloc fails, failure is
	 indicated by returning -1 and setting *errnoptr to EINVAL.

*/
int __myfs_readdir_implem(void *fileptr, size_t systemSize, int *errnoptr,
													const char *path, char ***namesptr) {
		Handler *fs;       // Handle to the file system
		Inode *inode;       // Inode to the given path
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		if (!inode->dirFile_check) {
				*errnoptr = ENOTDIR;
				return -1;
		}

		char *data = malloc(*(int*)(&inode->data_size_bytes) + 1);
		size_t data_size = data_to_buf(fs, inode, data);
		memcpy(data + data_size + 1, num_of_end, 1);
		char *temp, *name, *next;
		size_t name_count = 0;
		size_t name_len = 0;
		char *names = malloc(0);
		next = name = data;
		while ((temp = strsep(&next, num_of_end))) {
				if (!next || *temp <= 64 || !inode_char_check(*temp)) break;
				name = temp;                               // Extract file/dir name
				name = strsep(&name, dir_separator);
				int nlen = strlen(name) + 1;                // +1 for null term
				name_len += nlen;            
				names = realloc(names, name_len);  
				memcpy(names + name_len - nlen, name, nlen - 1);
				memset(names + name_len - 1, '\0', 1);
				name_count++;
		}

		*namesptr = calloc(name_count, 1);
		if (!namesptr) {
				*errnoptr = EFAULT;
		}
		else {
				char **curr = *namesptr;  // To keep namesptr static as we iterate
				next = names;
				for (int i = 0; i < name_count; i++)
				{
						int len = str_len(next);
						*curr = realloc(*curr, len + 1);
						strcpy(*curr, next);
						next += len+1;
			curr++;
				}
		}		
		free(data);
		return name_count;
}

/* -- __myfs_mknod_implem -- */
/* Implements an emulation of the mknod system call for regular files
	 on the filesystem of size systemSize pointed to by fileptr.

	 This function is called only for the creation of regular files.

	 If a file gets created, it is of size zero and has default
	 ownership and mode bits.

	 The call creates the file indicated by path.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 mknod.

*/
int __myfs_mknod_implem(void *fileptr, size_t systemSize, int *errnoptr,
												const char *path) {
		Handler *fs;       // Handle to the file system

		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 

		// Ensure file does not already exist
		if (resolve_fspath(fs, path, errnoptr)) {
				*errnoptr = EEXIST;
				return -1;
		}

		char *abspath, *fname, *begin, *temp, *next;
		
		begin = next = strdup(path);    // manipulation allowed
		next++;                        
		abspath = malloc(1);            
		*abspath = '\0';
		while ((temp = strsep(&next, path_separator)))
				if (!next) {
						fname = temp;
				} else {
						abspath = realloc(abspath, str_len(abspath) + str_len(temp) + 1);
						strcat(abspath, path_separator);
						strcat(abspath, temp);
				}
		// If parent is root dir
		if (*abspath == '\0')
				strcat(abspath, path_separator);
		Inode *newfile = create_file(fs, abspath, fname, "", 0);
		free(abspath);
		free(begin);
		if (!newfile) {
				*errnoptr = EINVAL;
				return -1;  
		}
		return 0;       // Success
}

/* -- __myfs_unlink_implem -- */
/* Implements an emulation of the unlink system call for regular files
	 on the filesystem of size systemSize pointed to by fileptr.

	 This function is called only for the deletion of regular files.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 unlink.

*/
int __myfs_unlink_implem(void *fileptr, size_t systemSize, int *errnoptr,
												const char *path) {
		Handler *fs;       
		Inode *inode;      
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		if (inode->dirFile_check || !remove_directory(fs, path)) {
				*errnoptr = EINVAL;
				return -1;  
		}

		return 0;  // Success
}

/* -- __myfs_rmdir_implem -- */
/* Implements an emulation of the rmdir system call on the filesystem 
	 of size systemSize pointed to by fileptr. 

	 The call deletes the directory indicated by path.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The function call must fail when the directory indicated by path is
	 not empty (if there are files or subdirectories other than . and ..).

	 The error codes are documented in man 2 rmdir.

*/
int __myfs_rmdir_implem(void *fileptr, size_t systemSize, int *errnoptr,
												const char *path) {
		Handler *fs;       // Handle
		Inode *inode;       
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		if (inode->data_size_bytes)  {
				*errnoptr = ENOTEMPTY;
				return -1;  // Fail
		}
		if (!remove_directory(fs, path)) {
				*errnoptr = EINVAL;
				return -1;  
		}
		return 0;  // Success
}

/* -- __myfs_mkdir_implem -- */
/* Implements an emulation of the mkdir system call on the filesystem 
	 of size systemSize pointed to by fileptr. 

	 The call creates the directory indicated by path.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 mkdir.

*/
int __myfs_mkdir_implem(void *fileptr, size_t systemSize, int *errnoptr,
												const char *path) {
		Handler *fs;       // Handle
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1;
		if (resolve_fspath(fs, path, errnoptr)) {
				*errnoptr = EEXIST;
				return -1;
		}
		char *parent_path, *name, *begin, *temp, *next;
		begin = next = strdup(path);    // Duplicate path
		next++;                         
		parent_path = malloc(1);           // Parent 
		*parent_path = '\0';
		while ((temp = strsep(&next, path_separator)))
				if (!next) {
						name = temp;
				} else {
						parent_path = realloc(parent_path, str_len(parent_path) + str_len(temp) + 1);
						strcat(parent_path, path_separator);
						strcat(parent_path, temp);
				}
		if (*parent_path == '\0')
				strcat(parent_path, path_separator);
		Inode *parent = resolve_fspath(fs, parent_path, errnoptr);
		Inode *newdir = create_directory(fs, parent, name);
		free(parent_path);
		free(begin);
		if (!newdir) {
				*errnoptr = EINVAL;
				return -1;  
		}

		return 0;       // Success
}
/* Implements an emulation of the rename system call on the filesystem 
	 of size systemSize pointed to by fileptr. 

	 The call moves the file or directory indicated by from to to.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

		Behavior (from man 2 readme):
		If  newpath  already  exists,  it  will   be   atomically
		replaced,  so  that  there  is  no point at which another
		process attempting to access newpath will find  it  miss‐
		ing.   However,  there will probably be a window in which
		both oldpath and newpath refer to the file being renamed.

		If oldpath and newpath are existing hard links  referring
		to the same file, then rename() does nothing, and returns
		a success status.

		If newpath exists but the operation fails for  some  rea‐
		son,  rename() guarantees to leave an instance of newpath
		in place.

		oldpath can specify a directory.  In this  case,  newpath
		must either not exist, or it must specify an empty direc‐
		tory.

		If oldpath  refers  to  a  symbolic  link,  the  link  is
		renamed;  if  newpath refers to a symbolic link, the link
		will be overwritten.

	 The error codes are documented in man 2 rename.

*/
int __myfs_rename_implem(void *fileptr, size_t systemSize, int *errnoptr,
												 const char *source, const char *destination) {
		if (strcmp(source, destination) == 0) return 0;  
		
		Handler *fs;           // Handle 
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		size_t from_len, to_len;
		size_t source_index = str_name_offset(source, &from_len);
		size_t destination_index = str_name_offset(destination, &to_len);
		char *source_path = strndup(source, (source_index > 1 ) ? source_index-1 : source_index);
		char *source_name = strndup(source + source_index, from_len - source_index);
		char *destination_path = strndup(destination, destination_index);
		char *destination_name = strndup(destination + destination_index, to_len - destination_index);
		Inode *source_parent = resolve_fspath(fs, source_path, errnoptr);
		Inode *destination_parent = resolve_fspath(fs, destination_path, errnoptr);
		Inode *source_child = resolve_fspath(fs, source, errnoptr);
		Inode *destination_child = resolve_fspath(fs, destination, errnoptr);
		free(source_name);
		free(source_path);
		if (!source_parent || !source_child || !destination_parent) {
				*errnoptr = EINVAL;
				free(destination_name);
				free(destination_path);
				return -1;
		}
		char *data = malloc(*(int*)(&source_child->data_size_bytes));
		size_t file_data; 
		if(source_child->dirFile_check) {
				if(!destination_child) {
						// printf("Moving !child\n");
						Inode *dest = create_directory(fs, destination_parent, destination_name);  // Create dest
						file_data = data_to_buf(fs, source_child, data);      // Get dir's data
						set_data(fs, dest, data, file_data);             // Copy to dest
						remove_directory(fs, source);                         // Remove old dir
				} 	
				else if (destination_child->dirFile_check && !destination_child->data_size_bytes) {
						// printf("moving: to empty existing dir\n");
						file_data = data_to_buf(fs, source_child, data);      // Get dir's data
						set_data(fs, destination_child, data, file_data);         // Overwrite dest
						remove_directory(fs, source);                         // Remove old dir
				}				
				else {
						*errnoptr = EINVAL;
						free(data);
						free(destination_name);
						free(destination_path);
						return -1;
				}
		}

		else {
				file_data = data_to_buf(fs, source_child, data);          // data
				
				if(destination_child)
						set_data(fs, destination_child, data, file_data);         // TODO: Atomic
				else 
						create_file(fs, destination_path, destination_name, data, file_data);
				remove_directory(fs, source);                             
		}

		free(data);
		free(destination_name);
		free(destination_path);
		return 0;  // Success
}

/* Implements an emulation of the truncate system call on the filesystem 
	 of size systemSize pointed to by fileptr. 

	 The call changes the size of the file indicated by path to offset
	 bytes.

	 When the file becomes smaller due to the call, the extending bytes are
	 removed. When it becomes larger, zeros are appended.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 truncate.

*/
int __myfs_truncate_implem(void *fileptr, size_t systemSize, int *errnoptr,
													 const char *path, off_t offset) {
		Handler *fs;       // Handle
		Inode *inode;       // Inode
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		char* initialSize = malloc(*(int*)(&inode->data_size_bytes));
		size_t data_size = data_to_buf(fs, inode, initialSize);
		if (offset > data_size) {
				size_t tempSize = offset- data_size;
				char *newSize = malloc(tempSize);
				memset(newSize, 0, tempSize);
				append(fs, inode, newSize);  // Pad w/zeroes
				free(newSize);
		}
		else if (offset < data_size) {
				set_data(fs, inode, initialSize, offset);
		}
		return 0;  // Success
}
/* -- __myfs_open_implem -- */
/* Implements an emulation of the open system call on the filesystem 
	 of size systemSize pointed to by fileptr, without actually performing the opening
	 of the file (no file descriptor is returned).

	 The call just checks if the file (or directory) indicated by path
	 can be accessed, i.e. if the path can be followed to an existing
	 object for which the access rights are granted.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The two only interesting error codes are 

	 * EFAULT: the filesystem is in a bad state, we can't do anything

	 * ENOENT: the file that we are supposed to open doesn't exist (or a
						 subpath).

	 It is possible to restrict ourselves to only these two error
	 conditions. It is also possible to implement more detailed error
	 condition answers.

	 The error codes are documented in man 2 open.

*/
int __myfs_open_implem(void *fileptr, size_t systemSize, int *errnoptr,
											 const char *path) {
		Handler *fs;       // Handle 
		Inode *inode;       // Inode 
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		return 0; // Success
}

/* -- __myfs_read_implem -- */
/* Implements an emulation of the read system call on the filesystem 
	 of size systemSize pointed to by fileptr.

	 The call copies up to size bytes from the file indicated by 
	 path into the buffer, starting to read at offset. See the man page
	 for read for the details when offset is beyond the end of the file etc.
	 
	 On success, the appropriate number of bytes read into the buffer is
	 returned. The value zero is returned on an end-of-file condition.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 read.

*/
int __myfs_read_implem(void *fileptr, size_t systemSize, int *errnoptr,
											 const char *path, char *buf, size_t size, off_t offset) {
		if (!size) return 0;    // If no bytes to read

		Handler *fs;           // Handle 
		Inode *inode;           // Inode 
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;	
		// Read 
		char* buffer = malloc(*(int*)(&inode->data_size_bytes));
		char *buffer2 = buffer;
		int buffer2_size = 0;
		size_t data_size = data_to_buf(fs, inode, buffer);
		if (offset <= data_size) {
				buffer2 += offset;              // data index
				buffer2_size = data_size - offset;  // bytes to read
				memcpy(buf, buffer2, buffer2_size); 
		}
		else {
						*errnoptr = EFBIG;          // Max offset exceeded
		}

		free(buffer);
		return buffer2_size;  // Success
}

/* -- __myfs_write_implem -- */
/* Implements an emulation of the write system call on the filesystem 
	 of size systemSize pointed to by fileptr.

	 The call copies up to size bytes to the file indicated by 
	 path into the buffer, starting to write at offset. See the man page
	 for write for the details when offset is beyond the end of the file etc.
	 
	 On success, the appropriate number of bytes written into the file is
	 returned. The value zero is returned on an end-of-file condition.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 write.
*/
int __myfs_write_implem(void *fileptr, size_t systemSize, int *errnoptr,
												const char *path, const char *buf, size_t size, off_t offset) {
		if (!size) return 0;  

		Handler *fs;       // Handle 
		Inode *inode;       // Inode 
		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		if (!offset) {
				char *copy = strndup(buf, size);
				set_data(fs, inode, copy, size);
				free(copy);
		}
		
		else {   
				int new_data_size;
				char *new_data;
				char *initialSize = malloc(*(int*)(&inode->data_size_bytes));
				size_t old_offset = data_to_buf(fs, inode, initialSize);
				if (offset <= old_offset) { 
						new_data = strndup(initialSize, offset);
						new_data_size = offset + size;
						new_data = realloc(new_data, new_data_size);
						memcpy(new_data + offset, buf, size);
						set_data(fs, inode, new_data, new_data_size);
						free(new_data);
				} 
				else {
						*errnoptr = EFBIG;
						size = 0; // Set return value
				}

				free(initialSize);
		}

		return size;  // num bytes written
}

/* -- __myfs_utimens_implem -- */
/* Implements an emulation of the utimensat system call on the filesystem 
	 of size systemSize pointed to by fileptr.

	 The call changes the access and modification times of the file
	 or directory indicated by path to the values in ts.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 utimensat.

*/
int __myfs_utimens_implem(void *fileptr, size_t systemSize, int *errnoptr,
													const char *path, const struct timespec ts[2]) {
		Handler *fs;       // Handle 
		Inode *inode;       // Inode 

		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 
		if ((!(inode = resolve_fspath(fs, path, errnoptr)))) return -1;
		memcpy(inode->last_accessTime, &ts[0], sizeof(struct timespec));
		memcpy(inode->last_time_modified, &ts[1], sizeof(struct timespec));
		
		return 0;
}

/* -- __myfs_statfs_implem -- */
/* Implements an emulation of the statfs system call on the filesystem 
	 of size systemSize pointed to by fileptr.

	 The call gets information of the filesystem usage and puts in 
	 into stbuf.

	 On success, 0 is returned.

	 On failure, -1 is returned and *errnoptr is set appropriately.

	 The error codes are documented in man 2 statfs.

	 Essentially, only the following fields of struct statvfs need to be
	 supported:

	 f_bsize   fill with what you call a block (typically 1024 bytes)
	 f_blocks  fill with the total number of blocks in the filesystem
	 f_bfree   fill with the free number of blocks in the filesystem
	 f_bavail  fill with same value as f_bfree
	 f_namemax fill with your maximum file/directory name, if your
						 filesystem has such a maximum

*/
int __myfs_statfs_implem(void *fileptr, size_t systemSize, int *errnoptr,
												 struct statvfs *stbuf) {
		Handler *fs;       // Handle 

		if ((!(fs = fs_handle(fileptr, systemSize, errnoptr)))) return -1; 

		size_t blocks_free = num_of_free(fs);
		stbuf->f_bsize = data_input;
		stbuf->f_blocks = 0;
		stbuf->f_bfree = blocks_free;
		stbuf->f_bavail = blocks_free;
		stbuf->f_namemax = 256;

		return 0;
}
