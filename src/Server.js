import {xu, fg} from "xu";
import {validateClass} from "validator";

export class Server
{
	serverid = this.constructor.name;
	baseKeys = Object.keys(this);

	// builder to get around the fact that constructors can't be async
	static create(xlog)
	{
		const server = new this();
		server.xlog = xlog.clone();
		server.xlog.mapper = v => `${xu.colon(fg.peach(server.serverid))}${v}`;

		validateClass(server, {
			// required
			serverid : {type : "string", required : true}, 	// automatically set to the constructor name
			start    : {type : "function", length : 0, required : true},
			status   : {type : "function", length : 0, required : true},
			stop     : {type : "function", length : 0, required : true},
			xlog     : {}
		});

		return server;
	}
}
