package schema_test

import (
	"testing"

	"github.com/stretchr/testify/assert"
	p "github.com/texm/prosemirror-go"
	"github.com/texm/prosemirror-go/schema"
)

func TestDefaultSchema(t *testing.T) {
	s := p.Must(p.NewSchema(schema.DefaultSpec))

	// test that text nodes can be created and are valid inside the top node
	if err := s.Nodes["doc"].CheckContent(p.NewFragment(s.Node("paragraph", nil, p.NewFragment(s.Text("hello"))))); err != nil {
		assert.NoError(t, err, "error creating text node")
	}
}

var (
	testNodes = map[p.NodeTypeName]p.NodeSpec{
		"doc": {
			Content: "block+",
		},
		"paragraph": {
			Content: "inline*",
			Group:   "block",
		},
		"text": {
			Group: "inline",
		},
		"listItem": {Content: "paragraph block*"},
	}
	testSpec = p.SchemaSpec{
		TopNode: "doc",
		Nodes:   testNodes,
		Marks:   schema.DefaultMarks,
	}
)

func TestSeqSchema(t *testing.T) {
	s := p.Must(p.NewSchema(testSpec))

	// test that text nodes can be created and are valid inside the top node
	if err := s.Nodes["doc"].CheckContent(p.NewFragment(s.Node("paragraph", nil, p.NewFragment(s.Text("hello"))))); err != nil {
		assert.NoError(t, err, "error creating text node")
	}
}
