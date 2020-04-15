/*
Copyright 2015 The Kubernetes Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package jsonpath

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"reflect"
	"strings"

	"k8s.io/client-go/third_party/forked/golang/template"
	"k8s.io/client-go/util/jsonpath/internal/fmtsort"
)

type JSONPath struct {
	name       string
	parser     *Parser
	stack      [][]reflect.Value // push and pop values in different scopes
	cur        []reflect.Value   // current scope values
	beginRange int
	inRange    int
	endRange   int

	allowMissingKeys bool
}

// New creates a new JSONPath with the given name.
func New(name string) *JSONPath {
	return &JSONPath{
		name:       name,
		beginRange: 0,
		inRange:    0,
		endRange:   0,
	}
}

// AllowMissingKeys allows a caller to specify whether they want an error if a field or map key
// cannot be located, or simply an empty result. The receiver is returned for chaining.
func (j *JSONPath) AllowMissingKeys(allow bool) *JSONPath {
	j.allowMissingKeys = allow
	return j
}

// Parse parses the given template and returns an error.
func (j *JSONPath) Parse(text string) error {
	var err error
	j.parser, err = Parse(j.name, text)
	return err
}

// Execute bounds data into template and writes the result.
func (j *JSONPath) Execute(wr io.Writer, data interface{}) error {
	fullResults, err := j.FindResults(data)
	if err != nil {
		return err
	}
	for ix := range fullResults {
		if err := j.PrintResults(wr, fullResults[ix]); err != nil {
			return err
		}
	}
	return nil
}

func (j *JSONPath) FindResults(data interface{}) ([][]reflect.Value, error) {
	if j.parser == nil {
		return nil, fmt.Errorf("%s is an incomplete jsonpath template", j.name)
	}

	j.cur = []reflect.Value{reflect.ValueOf(data)}
	nodes := j.parser.Root.Nodes
	fullResult := [][]reflect.Value{}
	for i := 0; i < len(nodes); i++ {
		node := nodes[i]
		results, err := j.walk(j.cur, node)
		if err != nil {
			return nil, err
		}

		// encounter an end node, break the current block
		if j.endRange > 0 && j.endRange <= j.inRange {
			j.endRange--
			break
		}
		// encounter a range node, start a range loop
		if j.beginRange > 0 {
			j.beginRange--
			j.inRange++
			for k, value := range results {
				j.parser.Root.Nodes = nodes[i+1:]
				if k == len(results)-1 {
					j.inRange--
				}
				nextResults, err := j.FindResults(value.Interface())
				if err != nil {
					return nil, err
				}
				fullResult = append(fullResult, nextResults...)
			}
			break
		}
		fullResult = append(fullResult, results)
	}
	return fullResult, nil
}

// PrintResults writes the results into writer
func (j *JSONPath) PrintResults(wr io.Writer, results []reflect.Value) error {
	for i, r := range results {
		var text []byte
		var err error
		outputJSON := true
		kind := r.Kind()
		if kind == reflect.Interface {
			kind = r.Elem().Kind()
		}
		switch kind {
		case reflect.Map:
		case reflect.Array:
		case reflect.Slice:
		case reflect.Struct:
		default:
			outputJSON = false
		}
		if outputJSON {
			text, err = json.Marshal(r.Interface())
		} else {
			text, err = j.evalToText(r)
		}
		if err != nil {
			return err
		}
		if i != len(results)-1 {
			text = append(text, ' ')
		}
		if _, err = wr.Write(text); err != nil {
			return err
		}
	}
	return nil

}

// walk visits tree rooted at the given node in DFS order
func (j *JSONPath) walk(value []reflect.Value, node Node) ([]reflect.Value, error) {
	switch node := node.(type) {
	case *ListNode:
		return j.evalList(value, node)
	case *TextNode:
		return []reflect.Value{reflect.ValueOf(node.Text)}, nil
	case *FieldNode:
		return j.evalField(value, node)
	case *ArrayNode:
		return j.evalArray(value, node)
	case *FilterNode:
		return j.evalFilter(value, node)
	case *IntNode:
		return j.evalInt(value, node)
	case *BoolNode:
		return j.evalBool(value, node)
	case *FloatNode:
		return j.evalFloat(value, node)
	case *WildcardNode:
		return j.evalWildcard(value, node)
	case *RecursiveNode:
		return j.evalRecursive(value, node)
	case *UnionNode:
		return j.evalUnion(value, node)
	case *IdentifierNode:
		return j.evalIdentifier(value, node)
	default:
		return value, fmt.Errorf("unexpected Node %v", node)
	}
}

// evalInt evaluates IntNode
func (j *JSONPath) evalInt(input []reflect.Value, node *IntNode) ([]reflect.Value, error) {
	result := make([]reflect.Value, len(input))
	for i := range input {
		result[i] = reflect.ValueOf(node.Value)
	}
	return result, nil
}

// evalFloat evaluates FloatNode
func (j *JSONPath) evalFloat(input []reflect.Value, node *FloatNode) ([]reflect.Value, error) {
	result := make([]reflect.Value, len(input))
	for i := range input {
		result[i] = reflect.ValueOf(node.Value)
	}
	return result, nil
}

// evalBool evaluates BoolNode
func (j *JSONPath) evalBool(input []reflect.Value, node *BoolNode) ([]reflect.Value, error) {
	result := make([]reflect.Value, len(input))
	for i := range input {
		result[i] = reflect.ValueOf(node.Value)
	}
	return result, nil
}

// evalList evaluates ListNode
func (j *JSONPath) evalList(value []reflect.Value, node *ListNode) ([]reflect.Value, error) {
	var err error
	curValue := value
	for _, node := range node.Nodes {
		curValue, err = j.walk(curValue, node)
		if err != nil {
			return curValue, err
		}
	}
	return curValue, nil
}

// evalIdentifier evaluates IdentifierNode
func (j *JSONPath) evalIdentifier(input []reflect.Value, node *IdentifierNode) ([]reflect.Value, error) {
	results := []reflect.Value{}
	switch node.Name {
	case "range":
		j.stack = append(j.stack, j.cur)
		j.beginRange++
		results = input
	case "end":
		if j.endRange < j.inRange { // inside a loop, break the current block
			j.endRange++
			break
		}
		// the loop is about to end, pop value and continue the following execution
		if len(j.stack) > 0 {
			j.cur, j.stack = j.stack[len(j.stack)-1], j.stack[:len(j.stack)-1]
		} else {
			return results, fmt.Errorf("not in range, nothing to end")
		}
	default:
		return input, fmt.Errorf("unrecognized identifier %v", node.Name)
	}
	return results, nil
}

// evalArray evaluates ArrayNode
func (j *JSONPath) evalArray(input []reflect.Value, node *ArrayNode) ([]reflect.Value, error) {
	result := []reflect.Value{}
	for _, value := range input {

		value, isNil := template.Indirect(value)
		if isNil {
			continue
		}
		if value.Kind() != reflect.Array && value.Kind() != reflect.Slice {
			return input, fmt.Errorf("%v is not array or slice", value.Type())
		}
		params := node.Params
		if !params[0].Known {
			params[0].Value = 0
		}
		if params[0].Value < 0 {
			params[0].Value += value.Len()
		}
		if !params[1].Known {
			params[1].Value = value.Len()
		}

		if params[1].Value < 0 || (params[1].Value == 0 && params[1].Derived) {
			params[1].Value += value.Len()
		}
		sliceLength := value.Len()
		if params[1].Value != params[0].Value { // if you're requesting zero elements, allow it through.
			if params[0].Value >= sliceLength || params[0].Value < 0 {
				return input, fmt.Errorf("array index out of bounds: index %d, length %d", params[0].Value, sliceLength)
			}
			if params[1].Value > sliceLength || params[1].Value < 0 {
				return input, fmt.Errorf("array index out of bounds: index %d, length %d", params[1].Value-1, sliceLength)
			}
			if params[0].Value > params[1].Value {
				return input, fmt.Errorf("starting index %d is greater than ending index %d", params[0].Value, params[1].Value)
			}
		} else {
			return result, nil
		}

		value = value.Slice(params[0].Value, params[1].Value)

		step := 1
		if params[2].Known {
			if params[2].Value <= 0 {
				return input, fmt.Errorf("step must be > 0")
			}
			step = params[2].Value
		}
		for i := 0; i < value.Len(); i += step {
			result = append(result, value.Index(i))
		}
	}
	return result, nil
}

// evalUnion evaluates UnionNode
func (j *JSONPath) evalUnion(input []reflect.Value, node *UnionNode) ([]reflect.Value, error) {
	result := []reflect.Value{}
	for _, listNode := range node.Nodes {
		temp, err := j.evalList(input, listNode)
		if err != nil {
			return input, err
		}
		result = append(result, temp...)
	}
	return result, nil
}

func (j *JSONPath) findFieldInValue(value *reflect.Value, node *FieldNode) (reflect.Value, error) {
	t := value.Type()
	var inlineValue *reflect.Value
	for ix := 0; ix < t.NumField(); ix++ {
		f := t.Field(ix)
		jsonTag := f.Tag.Get("json")
		parts := strings.Split(jsonTag, ",")
		if len(parts) == 0 {
			continue
		}
		if parts[0] == node.Value {
			return value.Field(ix), nil
		}
		if len(parts[0]) == 0 {
			val := value.Field(ix)
			inlineValue = &val
		}
	}
	if inlineValue != nil {
		if inlineValue.Kind() == reflect.Struct {
			// handle 'inline'
			match, err := j.findFieldInValue(inlineValue, node)
			if err != nil {
				return reflect.Value{}, err
			}
			if match.IsValid() {
				return match, nil
			}
		}
	}
	return value.FieldByName(node.Value), nil
}

// evalField evaluates field of struct or key of map.
func (j *JSONPath) evalField(input []reflect.Value, node *FieldNode) ([]reflect.Value, error) {
	results := []reflect.Value{}
	// If there's no input, there's no output
	if len(input) == 0 {
		return results, nil
	}
	for _, value := range input {
		var result reflect.Value
		value, isNil := template.Indirect(value)
		if isNil {
			continue
		}

		if value.Kind() == reflect.Struct {
			var err error
			if result, err = j.findFieldInValue(&value, node); err != nil {
				return nil, err
			}
		} else if value.Kind() == reflect.Map {
			mapKeyType := value.Type().Key()
			nodeValue := reflect.ValueOf(node.Value)
			// node value type must be convertible to map key type
			if !nodeValue.Type().ConvertibleTo(mapKeyType) {
				return results, fmt.Errorf("%s is not convertible to %s", nodeValue, mapKeyType)
			}
			result = value.MapIndex(nodeValue.Convert(mapKeyType))
		}
		if result.IsValid() {
			results = append(results, result)
		}
	}
	if len(results) == 0 {
		if j.allowMissingKeys {
			return results, nil
		}
		return results, fmt.Errorf("%s is not found", node.Value)
	}
	return results, nil
}

// evalWildcard extracts all contents of the given value
func (j *JSONPath) evalWildcard(input []reflect.Value, node *WildcardNode) ([]reflect.Value, error) {
	results := []reflect.Value{}
	for _, value := range input {
		value, isNil := template.Indirect(value)
		if isNil {
			continue
		}

		iterable, indexFunc, length := iterHelper(value)
		if !iterable {
			continue
		}
		for i := 0; i < length; i++ {
			results = append(results, indexFunc(i))
		}
	}
	return results, nil
}

// valueIndexFunc is a type used for function closures that wrap an interable reflect.Value
type valueIndexFunc func(index int) reflect.Value

// iterHelper accepts a reflect.Value and returns
// whether it is iterable, a function to access each instance by index, and length
// Note: only Array/Slice/Struct/Map are considered iterable for use in jsonpath
func iterHelper(value reflect.Value) (iterable bool, valueIndexFunc valueIndexFunc, length int) {
	wrappedValue := value
	iterable = true
	switch value.Kind() {
	case reflect.Array:
		// original order is maintained
		length = value.Len()
		valueIndexFunc = func(i int) reflect.Value {
			return wrappedValue.Index(i)
		}
	case reflect.Slice:
		// original order is maintained
		length = value.Len()
		valueIndexFunc = func(i int) reflect.Value {
			return wrappedValue.Index(i)
		}
	case reflect.Struct:
		// field order is maintained
		length = value.NumField()
		valueIndexFunc = func(i int) reflect.Value {
			return wrappedValue.Field(i)
		}
	case reflect.Map:
		// keys are sorted based on the primitive type using internal/fmtsort
		orderedMap := fmtsort.Sort(value)
		length = orderedMap.Len()
		valueIndexFunc = func(i int) reflect.Value {
			return orderedMap.Value[i]
		}
	default:
		iterable = false
	}
	return
}

// evalRecursive visits the given value recursively and pushes all of them to result
func (j *JSONPath) evalRecursive(input []reflect.Value, node *RecursiveNode) ([]reflect.Value, error) {
	result := []reflect.Value{}
	for _, value := range input {
		results := []reflect.Value{}
		value, isNil := template.Indirect(value)
		if isNil {
			continue
		}

		iterable, indexFunc, length := iterHelper(value)
		if !iterable {
			continue
		}
		for i := 0; i < length; i++ {
			results = append(results, indexFunc(i))
		}

		if len(results) != 0 {
			result = append(result, value)
			output, err := j.evalRecursive(results, node)
			if err != nil {
				return result, err
			}
			result = append(result, output...)
		}
	}
	return result, nil
}

func evalOperator(operator string, l reflect.Value, r reflect.Value) (pass bool, err error) {
	var left, right interface{}
	left = l.Interface()
	right = r.Interface()
	if reflect.ValueOf(left).Kind() == reflect.Int {
		left = float64(left.(int))
	}
	if reflect.ValueOf(right).Kind() == reflect.Int {
		right = float64(right.(int))
	}
	switch operator {
	case "<":
		pass, err = template.Less(left, right)
	case ">":
		pass, err = template.Greater(left, right)
	case "==":
		pass, err = template.Equal(left, right)
	case "!=":
		pass, err = template.NotEqual(left, right)
	case "<=":
		pass, err = template.LessEqual(left, right)
	case ">=":
		pass, err = template.GreaterEqual(left, right)
	default:
		return false, fmt.Errorf("unrecognized filter operator %s", operator)
	}
	// ignore comparisons for incompatible types
	if err != nil && !(err.Error() == "invalid type for comparison" ||
		err.Error() == "incompatible types for comparison") {
		return false, err
	}
	return pass, nil
}

// evalFilter filters array according to FilterNode
func (j *JSONPath) evalFilter(input []reflect.Value, node *FilterNode) ([]reflect.Value, error) {
	results := []reflect.Value{}
	for _, value := range input {
		value, _ = template.Indirect(value)

		iterable, indexFunc, length := iterHelper(value)

		// if the object isn't iterable, provide a dummy index function
		if !iterable {
			indexFunc = func(i int) reflect.Value {
				return value
			}
			length = 1
		}
		for i := 0; i < length; i++ {
			temp := []reflect.Value{indexFunc(i)}
			lefts, err := j.evalList(temp, node.Left)
			if err != nil && !j.allowMissingKeys {
				return input, err
			}
			rights, err := j.evalList(temp, node.Right)
			if err != nil {
				return input, err
			}

			switch {
			case len(lefts) == 0:
				continue
			case len(lefts) > 1:
				return input, fmt.Errorf("can only compare one element at a time")
			case node.Operator == "exists":
				results = append(results, indexFunc(i))
				continue
			case len(rights) == 0:
				continue
			case len(rights) > 1:
				return input, fmt.Errorf("can only compare one element at a time")
			}

			pass, err := evalOperator(node.Operator, lefts[0], rights[0])
			if err != nil {
				return results, err
			}
			if pass {
				results = append(results, indexFunc(i))
			}
		}
	}
	return results, nil
}

// evalToText translates reflect value to corresponding text
func (j *JSONPath) evalToText(v reflect.Value) ([]byte, error) {
	iface, ok := template.PrintableValue(v)
	if !ok {
		return nil, fmt.Errorf("can't print type %s", v.Type())
	}
	var buffer bytes.Buffer
	fmt.Fprint(&buffer, iface)
	return buffer.Bytes(), nil
}
