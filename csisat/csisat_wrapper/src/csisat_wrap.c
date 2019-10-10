/*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 */

#include "csisat_wrap.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
  
#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>

#include <jni.h> 


JNIEXPORT void JNICALL
Java_CSIsatWrap_initCaml(JNIEnv *env, jclass clazz)
{
  char *dummy[] = {0};
  caml_startup(dummy);
}

JNIEXPORT jstring JNICALL
Java_CSIsatWrap_interpolateString(JNIEnv *env, jclass clazz, jstring s)
{
  CAMLparam0();
  CAMLlocal1(ostr);

  static value *func;
  const char *str;
 
  if (!(str = (*env)->GetStringUTFChars(env, s, NULL))) return NULL;
  ostr = caml_copy_string(str);
  (*env)->ReleaseStringUTFChars(env, s, str);
  if (!func && !(func = caml_named_value("interpolate_string"))) return NULL;
  return (*env)->NewStringUTF(env, String_val(caml_callback(*func, ostr)));
}
